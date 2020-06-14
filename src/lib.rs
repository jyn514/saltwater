#![allow(clippy::cognitive_complexity)]
#![warn(absolute_paths_not_starting_with_crate)]
#![warn(explicit_outlives_requirements)]
#![warn(unreachable_pub)]
#![warn(deprecated_in_future)]
#![deny(unsafe_code)]
#![deny(unused_extern_crates)]

use std::collections::{HashMap, VecDeque};
use std::io;
use std::path::{Path, PathBuf};
use std::process::Command;
use std::rc::Rc;

pub use codespan;
#[cfg(feature = "codegen")]
use cranelift_module::{Backend, Module};

#[cfg(feature = "codegen")]
pub use ir::initialize_aot_module;

#[cfg(all(feature = "color-backtrace", not(feature = "cc")))]
compile_error!(concat!(
    "The color-backtrace feature does nothing unless used by the `",
    env!("CARGO_PKG_DIR"),
    "` binary."
));

/// The `Source` type for `codespan::Files`.
///
/// Used to store extra metadata about the file, like the absolute filename.
///
/// NOTE: If `path` is empty (e.g. by using `my_string.into()`),
/// then the path will be relative to the _compiler_, not to the current file.
/// This is recommended only for test code and proof of concepts,
/// since it does not adhere to the C standard.
#[derive(Debug, Clone)]
pub struct Source {
    pub code: Rc<str>,
    pub path: PathBuf,
}

impl AsRef<str> for Source {
    fn as_ref(&self) -> &str {
        self.code.as_ref()
    }
}

pub type Files = codespan::Files<Source>;
#[cfg(feature = "codegen")]
pub type Product = <cranelift_object::ObjectBackend as Backend>::Product;
/// A result which includes all warnings, even for `Err` variants.
///
/// If successful, this returns an `Ok(T)`.
/// If unsuccessful, this returns an `Err(E)`.
/// Regardless, this always returns all warnings found.
pub struct Program<T, E = VecDeque<CompileError>> {
    /// Either the errors found while compiling the program, or the successfully compiled program.
    pub result: Result<T, E>,
    /// The warnings emitted while compiling the program
    pub warnings: VecDeque<CompileWarning>,
    /// The files that were `#include`d by the preprocessor
    pub files: Files,
}

impl<T, E> Program<T, E> {
    fn from_cpp(mut cpp: PreProcessor, result: Result<T, E>) -> Self {
        Program {
            result,
            warnings: cpp.warnings(),
            files: cpp.into_files(),
        }
    }
}

pub use analyze::{analyze, Analyzer, PureAnalyzer};
pub use data::*;
// https://github.com/rust-lang/rust/issues/64762
#[allow(unreachable_pub)]
pub use lex::{Definition, Lexer, PreProcessor, PreProcessorBuilder};
pub use parse::Parser;

#[macro_use]
mod macros;
mod analyze;
mod arch;
pub mod data;
mod fold;
pub mod intern;
#[cfg(feature = "codegen")]
mod ir;
mod lex;
mod parse;

pub use lex::replace;

#[derive(Debug, thiserror::Error)]
pub enum Error {
    #[error("{}", .0.iter().map(|err| err.data.to_string()).collect::<Vec<_>>().join("\n"))]
    Source(VecDeque<CompileError>),
    #[cfg(feature = "codegen")]
    #[error("linking error: {0}")]
    Platform(cranelift_object::object::write::Error),
    #[error("io error: {0}")]
    IO(#[from] io::Error),
}

impl From<CompileError> for Error {
    fn from(err: CompileError) -> Error {
        Error::Source(vec_deque![err])
    }
}

impl From<VecDeque<CompileError>> for Error {
    fn from(errs: VecDeque<CompileError>) -> Self {
        Error::Source(errs)
    }
}

#[derive(Clone, Debug, Default)]
struct RecursionGuard(Rc<()>);

impl RecursionGuard {
    // this is just a guesstimate, it should probably be configurable
    #[cfg(debug_assertions)]
    const MAX_DEPTH: usize = 1000;
    #[cfg(not(debug_assertions))]
    const MAX_DEPTH: usize = 10000;

    // make sure we don't crash on highly nested expressions
    // or rather, crash in a controlled way
    fn recursion_check(&self, error_handler: &mut ErrorHandler) -> RecursionGuard {
        let guard = self.clone();
        let depth = Rc::strong_count(&guard.0);
        if depth > Self::MAX_DEPTH {
            Self::recursion_check_failed(depth, error_handler);
        }
        guard
    }

    #[cold]
    #[inline(never)]
    fn recursion_check_failed(depth: usize, mut error_handler: &mut ErrorHandler) -> ! {
        eprintln!(
            "fatal: maximum recursion depth exceeded ({} > {})",
            depth,
            Self::MAX_DEPTH
        );
        if !error_handler.is_empty() {
            println!("pending errors:");
            for error in &mut error_handler {
                println!("- error: {}", error.data);
            }
            for warning in &mut error_handler.warnings {
                println!("- warning: {}", warning.data);
            }
        }
        std::process::exit(102);
    }
}

#[derive(Default, Clone)]
pub struct Opt {
    /// If set, print all tokens found by the lexer in addition to compiling.
    pub debug_lex: bool,

    /// If set, print the parsed abstract syntax tree (AST) in addition to compiling
    ///
    /// The AST does no type checking or validation, it only parses.
    pub debug_ast: bool,

    /// If set, print the high intermediate representation (HIR) in addition to compiling
    ///
    /// This does type checking and validation and also desugars various expressions.
    /// For static initialization, it will also perform constant folding.
    pub debug_hir: bool,

    /// If set, print the intermediate representation of the program in addition to compiling
    pub debug_asm: bool,

    /// If set, compile and assemble but do not link. Object file is machine-dependent.
    pub no_link: bool,

    #[cfg(feature = "jit")]
    /// If set, compile and emit JIT code, and do not emit object files and binaries.
    pub jit: bool,

    /// The maximum number of errors to allow before giving up.
    /// If None, allows an unlimited number of errors.
    pub max_errors: Option<std::num::NonZeroUsize>,

    /// The directories to consider as part of the system search path.
    pub search_path: Vec<PathBuf>,

    /// The pre-defined macros to have as part of the preprocessor.
    pub definitions: HashMap<InternedStr, Definition>,

    /// The path of the original file.
    ///
    /// This allows looking for local includes relative to that file.
    /// An empty path is allowed but not recommended; it will cause the preprocessor
    /// to look for includes relative to the current directory of the process.
    pub filename: PathBuf,
}

/// Preprocess the source and return the tokens.
pub fn preprocess(buf: &str, opt: Opt) -> Program<VecDeque<Locatable<Token>>> {
    let path = opt.search_path.iter().map(|p| p.into());
    let mut cpp = PreProcessor::new(buf, opt.filename, opt.debug_lex, path, opt.definitions);

    let mut tokens = VecDeque::new();
    let mut errs = VecDeque::new();
    for result in &mut cpp {
        match result {
            Ok(token) => tokens.push_back(token),
            Err(err) => errs.push_back(err),
        }
    }
    let result = if errs.is_empty() {
        Ok(tokens)
    } else {
        Err(errs)
    };
    Program {
        result,
        warnings: cpp.warnings(),
        files: cpp.into_files(),
    }
}

/// Perform semantic analysis, including type checking and constant folding.
pub fn check_semantics(buf: &str, opt: Opt) -> Program<Vec<Locatable<hir::Declaration>>> {
    let path = opt.search_path.iter().map(|p| p.into());
    let mut cpp = PreProcessor::new(buf, opt.filename, opt.debug_lex, path, opt.definitions);

    let mut errs = VecDeque::new();

    macro_rules! handle_err {
        ($err: expr) => {{
            errs.push_back($err);
            if let Some(max) = opt.max_errors {
                if errs.len() >= max.into() {
                    return Program::from_cpp(cpp, Err(errs));
                }
            }
        }};
    }
    let first = loop {
        match cpp.next_non_whitespace() {
            Some(Ok(token)) => break Some(token),
            Some(Err(err)) => handle_err!(err),
            None => break None,
        }
    };

    let first = match first {
        Some(token) => token,
        None => {
            if errs.is_empty() {
                errs.push_back(cpp.eof().error(SemanticError::EmptyProgram));
            }
            return Program::from_cpp(cpp, Err(errs));
        }
    };

    let mut hir = vec![];
    let mut parser = Analyzer::new(Parser::new(first, &mut cpp, opt.debug_ast), opt.debug_hir);
    for res in &mut parser {
        match res {
            Ok(decl) => hir.push(decl),
            Err(err) => handle_err!(err),
        }
    }

    let mut warnings = parser.inner.warnings();
    warnings.extend(cpp.warnings());
    if hir.is_empty() && errs.is_empty() {
        errs.push_back(cpp.eof().error(SemanticError::EmptyProgram));
    }
    let result = if !errs.is_empty() { Err(errs) } else { Ok(hir) };
    Program {
        result,
        warnings,
        files: cpp.into_files(),
    }
}

#[cfg(feature = "codegen")]
/// Compile and return the declarations and warnings.
pub fn compile<B: Backend>(module: Module<B>, buf: &str, opt: Opt) -> Program<Module<B>> {
    let debug_asm = opt.debug_asm;
    let mut program = check_semantics(buf, opt);
    let hir = match program.result {
        Ok(hir) => hir,
        Err(err) => {
            return Program {
                result: Err(err),
                warnings: program.warnings,
                files: program.files,
            }
        }
    };
    let (result, ir_warnings) = ir::compile(module, hir, debug_asm);
    program.warnings.extend(ir_warnings);
    Program {
        result: result.map_err(|errs| vec_deque![errs]),
        warnings: program.warnings,
        files: program.files,
    }
}

#[cfg(feature = "codegen")]
pub fn assemble(product: Product, output: &Path) -> Result<(), Error> {
    use io::Write;
    use std::fs::File;

    let bytes = product.emit().map_err(Error::Platform)?;
    File::create(output)?
        .write_all(&bytes)
        .map_err(io::Error::into)
}

pub fn link(obj_file: &Path, output: &Path) -> Result<(), io::Error> {
    use std::io::{Error, ErrorKind};
    // link the .o file using host linker
    let status = Command::new("cc")
        .args(&[&obj_file, Path::new("-o"), output])
        .status()
        .map_err(|err| {
            if err.kind() == ErrorKind::NotFound {
                Error::new(
                    ErrorKind::NotFound,
                    "could not find host cc (for linking). Is it on your PATH?",
                )
            } else {
                err
            }
        })?;
    if !status.success() {
        Err(Error::new(ErrorKind::Other, "linking program failed"))
    } else {
        Ok(())
    }
}

#[cfg(feature = "jit")]
pub use jit::*;

#[cfg(feature = "jit")]
mod jit {
    use super::*;
    use crate::ir::get_isa;
    use cranelift_simplejit::{SimpleJITBackend, SimpleJITBuilder};
    use std::convert::TryFrom;

    pub fn initialize_jit_module() -> Module<SimpleJITBackend> {
        let libcall_names = cranelift_module::default_libcall_names();
        Module::new(SimpleJITBuilder::with_isa(get_isa(true), libcall_names))
    }

    /// Structure used to handle compiling C code to memory instead of to disk.
    ///
    /// You can use [`from_string`] to create a JIT instance.
    /// Alternatively, if you don't care about compile warnings, you can use `JIT::try_from` instead.
    /// If you already have a `Module`, you can use `JIT::from` to avoid having to `unwrap()`.
    ///
    /// JIT stands for 'Just In Time' compiled, the way that Java and JavaScript work.
    ///
    /// [`from_string`]: #method.from_string
    pub struct JIT {
        module: Module<SimpleJITBackend>,
    }

    impl From<Module<SimpleJITBackend>> for JIT {
        fn from(module: Module<SimpleJITBackend>) -> Self {
            Self { module }
        }
    }

    impl TryFrom<Rc<str>> for JIT {
        type Error = Error;
        fn try_from(source: Rc<str>) -> Result<JIT, Self::Error> {
            JIT::from_string(source, Opt::default()).result
        }
    }

    impl JIT {
        /// Compile string and return JITed code.
        pub fn from_string<R: Into<Rc<str>>>(source: R, opt: Opt) -> Program<Self, Error> {
            let source = source.into();
            let module = initialize_jit_module();
            let program = compile(module, &source, opt);
            let result = match program.result {
                Ok(module) => Ok(JIT::from(module)),
                Err(errs) => Err(errs.into()),
            };
            Program {
                result,
                warnings: program.warnings,
                files: program.files,
            }
        }

        /// Invoke this function before trying to get access to "new" compiled functions.
        pub fn finalize(&mut self) {
            self.module.finalize_definitions();
        }
        /// Get a compiled function. If this function doesn't exist then `None` is returned, otherwise its address returned.
        ///
        /// # Panics
        /// Panics if function is not compiled (finalized). Try to invoke `finalize` before using `get_compiled_function`.
        pub fn get_compiled_function(&mut self, name: &str) -> Option<*const u8> {
            use cranelift_module::FuncOrDataId;

            let name = self.module.get_name(name);
            if let Some(FuncOrDataId::Func(id)) = name {
                Some(self.module.get_finalized_function(id))
            } else {
                None
            }
        }
        /// Get compiled static data. If this data doesn't exist then `None` is returned, otherwise its address and size are returned.
        pub fn get_compiled_data(&mut self, name: &str) -> Option<(*mut u8, usize)> {
            use cranelift_module::FuncOrDataId;

            let name = self.module.get_name(name);
            if let Some(FuncOrDataId::Data(id)) = name {
                Some(self.module.get_finalized_data(id))
            } else {
                None
            }
        }
        /// Given a module, run the `main` function.
        ///
        /// This automatically calls `self.finalize()`.
        /// If `main()` does not exist in the module, returns `None`; otherwise returns the exit code.
        ///
        /// # Safety
        /// This function runs arbitrary C code.
        /// It can segfault, access out-of-bounds memory, cause data races, or do anything else C can do.
        #[allow(unsafe_code)]
        pub unsafe fn run_main(&mut self) -> Option<i32> {
            self.finalize();
            let main = self.get_compiled_function("main")?;
            let args = std::env::args().skip(1);
            let argc = args.len() as i32;
            // CString should be alive if we want to pass its pointer to another function,
            // otherwise this may lead to UB.
            let vec_args = args
                .map(|string| std::ffi::CString::new(string).unwrap())
                .collect::<Vec<_>>();
            // This vec needs to be stored so we aren't passing a pointer to a freed temporary.
            let argv = vec_args
                .iter()
                .map(|cstr| cstr.as_ptr() as *const u8)
                .collect::<Vec<_>>();
            assert_ne!(main, std::ptr::null());
            // this transmute is safe: this function is finalized (`self.finalize()`)
            // and **guaranteed** to be non-null
            let main: unsafe extern "C" fn(i32, *const *const u8) -> i32 =
                std::mem::transmute(main);
            // though transmute is safe, invoking this function is unsafe because we invoke C code.
            Some(main(argc, argv.as_ptr() as *const *const u8))
        }
    }
}

impl<T: Into<Rc<str>>> From<T> for Source {
    fn from(src: T) -> Self {
        Self {
            code: src.into(),
            path: PathBuf::new(),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    fn compile(src: &str) -> Result<Vec<hir::Declaration>, Error> {
        let options = Opt::default();
        let res = super::check_semantics(src, options).result;
        match res {
            Ok(decls) => Ok(decls.into_iter().map(|l| l.data).collect()),
            Err(errs) => Err(Error::Source(errs)),
        }
    }
    fn compile_err(src: &str) -> VecDeque<CompileError> {
        match compile(src).err().unwrap() {
            Error::Source(errs) => errs,
            _ => unreachable!(),
        }
    }
    #[test]
    fn empty() {
        let mut lex_errs = compile_err("`\n");
        assert!(lex_errs.pop_front().unwrap().data.is_lex_err());
        assert!(lex_errs.is_empty());

        let mut empty_errs = compile_err("");
        let err = empty_errs.pop_front().unwrap().data;
        assert_eq!(err, SemanticError::EmptyProgram.into());
        assert!(err.is_semantic_err());
        assert!(empty_errs.is_empty());

        let mut parse_err = compile_err("+++\n");
        let err = parse_err.pop_front();
        assert!(parse_err.is_empty());
        assert!(err.unwrap().data.is_syntax_err());
    }
}
