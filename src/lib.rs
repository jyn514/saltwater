#![allow(clippy::cognitive_complexity)]
#![warn(absolute_paths_not_starting_with_crate)]
#![warn(explicit_outlives_requirements)]
#![warn(unreachable_pub)]
#![warn(deprecated_in_future)]
#![deny(unused_extern_crates)]
#![deny(unsafe_code)]

use std::collections::VecDeque;
use std::fs::File;
use std::io::{self, Write};
use std::path::{Path, PathBuf};
use std::process::Command;

use cranelift::codegen::settings::{Configurable, Flags};
use cranelift_module::{Backend, Module};
use cranelift_object::{ObjectBackend, ObjectBuilder, ObjectTrapCollection};
#[cfg(feature = "jit")]
use cranelift_simplejit::{SimpleJITBackend, SimpleJITBuilder};
pub type Product = <ObjectBackend as Backend>::Product;

use data::prelude::CompileError;
pub use data::prelude::*;
pub use lex::PreProcessor;
pub use parse::Parser;

#[macro_use]
pub mod utils;
mod arch;
pub mod data;
mod fold;
pub mod intern;
mod ir;
mod lex;
mod parse;

#[derive(Debug)]
pub enum Error {
    Source(VecDeque<CompileError>),
    Platform(String),
    IO(io::Error),
}

impl From<io::Error> for Error {
    fn from(err: io::Error) -> Error {
        Error::IO(err)
    }
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

#[derive(Debug)]
pub struct Opt {
    /// The file where the C source came from
    pub filename: PathBuf,

    /// If set, print all tokens found by the lexer in addition to compiling.
    pub debug_lex: bool,

    /// If set, print the parsed abstract syntax tree in addition to compiling
    pub debug_ast: bool,

    /// If set, print the intermediate representation of the program in addition to compiling
    pub debug_asm: bool,

    /// If set, compile and assemble but do not link. Object file is machine-dependent.
    pub no_link: bool,
    /// If set, compile and emit JIT code, and do not emit object files and binaries.
    pub jit: bool,
    /// The maximum number of errors to allow before giving up.
    /// If None, allows an unlimited number of errors.
    pub max_errors: Option<std::num::NonZeroUsize>,
}

impl Default for Opt {
    fn default() -> Self {
        Opt {
            filename: "<default>".into(),
            debug_lex: false,
            debug_ast: false,
            debug_asm: false,
            no_link: false,
            max_errors: None,
            jit: false,
        }
    }
}

/// Preprocess the source and return the tokens.
///
/// Note on the return type:
/// If successful, this returns an `Ok(VecDeque<Token>)`.
/// The `VecDeque` is so you can iterate the tokens in order without consuming them.
/// If unsuccessful, this returns an `Err(VecDeque<Error>)`,
/// again so you can iterate the tokens in order.
/// Regardless, this always returns all warnings found.
#[allow(clippy::type_complexity)]
pub fn preprocess(
    buf: &str,
    opt: &Opt,
) -> (
    Result<VecDeque<Locatable<Token>>, VecDeque<CompileError>>,
    VecDeque<CompileWarning>,
) {
    let filename = opt.filename.to_string_lossy();
    let mut cpp = PreProcessor::new(filename, &buf, opt.debug_lex);

    let mut tokens = VecDeque::new();
    let mut errs = VecDeque::new();
    for result in &mut cpp {
        match result {
            Ok(token) => tokens.push_back(token),
            Err(err) => errs.push_back(err),
        }
    }
    let res = if errs.is_empty() {
        Ok(tokens)
    } else {
        Err(errs)
    };
    (res, cpp.warnings())
}

fn get_flags(jit: bool) -> Flags {
    let mut flags_builder = cranelift::codegen::settings::builder();
    if !jit {
        // allow creating shared libraries
        flags_builder
            .enable("is_pic")
            .expect("is_pic should be a valid option");
    }
    // use debug assertions
    flags_builder
        .enable("enable_verifier")
        .expect("enable_verifier should be a valid option");
    // minimal optimizations
    flags_builder
        .set("opt_level", "speed")
        .expect("opt_level: speed should be a valid option");
    // don't emit call to __cranelift_probestack
    flags_builder
        .set("enable_probestack", "false")
        .expect("enable_probestack should be a valid option");
    Flags::new(flags_builder)
}

#[cfg(feature = "jit")]
pub fn initialize_jit_module() -> Module<SimpleJITBackend> {
    let flags = get_flags(true);

    let isa = cranelift::codegen::isa::lookup(arch::TARGET)
        .unwrap_or_else(|_| utils::fatal(format!("platform not supported: {}", arch::TARGET), 5))
        .finish(flags);

    let builder = SimpleJITBuilder::with_isa(isa, cranelift_module::default_libcall_names());
    Module::new(builder)
}

pub fn initialize_aot_module(name: String) -> Module<ObjectBackend> {
    let flags = get_flags(false);

    let isa = cranelift::codegen::isa::lookup(arch::TARGET)
        .unwrap_or_else(|_| utils::fatal(format!("platform not supported: {}", arch::TARGET), 5))
        .finish(flags);

    let builder = ObjectBuilder::new(
        isa,
        name,
        ObjectTrapCollection::Disabled,
        cranelift_module::default_libcall_names(),
    )
    .expect("unknown error creating module");
    Module::new(builder)
}

/// Compile and return the declarations and warnings.
pub fn compile<B: Backend>(
    module: Module<B>,
    buf: &str,
    opt: &Opt,
) -> (Result<Module<B>, Error>, VecDeque<CompileWarning>) {
    let filename = opt.filename.to_string_lossy();
    let filename_ref = InternedStr::get_or_intern(filename.as_ref());
    let mut cpp = PreProcessor::new(filename, &buf, opt.debug_lex);

    let mut errs = VecDeque::new();

    macro_rules! handle_err {
        ($err: expr) => {{
            errs.push_back($err);
            if let Some(max) = opt.max_errors {
                if errs.len() >= max.into() {
                    return (Err(Error::Source(errs)), cpp.warnings());
                }
            }
        }};
    }
    let first = loop {
        match cpp.next() {
            Some(Ok(token)) => break Some(token),
            Some(Err(err)) => handle_err!(err),
            None => break None,
        }
    };
    let eof = || Location {
        span: (buf.len() as u32..buf.len() as u32).into(),
        filename: filename_ref,
    };

    let first = match first {
        Some(token) => token,
        None => {
            if errs.is_empty() {
                errs.push_back(eof().error(SemanticError::EmptyProgram));
            }
            return (Err(Error::Source(errs)), cpp.warnings());
        }
    };

    let mut hir = vec![];
    let mut parser = Parser::new(first, &mut cpp, opt.debug_ast);
    for res in &mut parser {
        match res {
            Ok(decl) => hir.push(decl),
            Err(err) => handle_err!(err),
        }
    }
    if hir.is_empty() && errs.is_empty() {
        errs.push_back(eof().error(SemanticError::EmptyProgram));
    }

    let mut warnings = parser.warnings();
    warnings.extend(cpp.warnings());
    if !errs.is_empty() {
        return (Err(Error::Source(errs)), warnings);
    }
    let (result, ir_warnings) = ir::compile(module, hir, opt.debug_asm);
    warnings.extend(ir_warnings);
    (result.map_err(Error::from), warnings)
}

pub fn assemble(product: Product, output: &Path) -> Result<(), Error> {
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

/// Structure used to handle compiling C code to memory instead of to disk.
///
/// You should use `JIT::from_module` or `JIT::compile_string` to create instance of JIT.
/// NOTE: JIT stands for 'Just In Time' compiled, the way that Java and JavaScript work.
#[cfg(feature = "jit")]
pub struct JIT {
    module: Module<SimpleJITBackend>,
}

#[cfg(feature = "jit")]
impl From<Module<SimpleJITBackend>> for JIT {
    fn from(module: Module<SimpleJITBackend>) -> Self {
        Self { module }
    }
}

#[cfg(feature = "jit")]
impl JIT {
    /// Compile string and return JITed code.
    pub fn from_string(
        program: &str,
        opt: &Opt,
    ) -> (Result<Self, Error>, VecDeque<CompileWarning>) {
        let module = initialize_jit_module();
        let (result, warnings) = compile::<SimpleJITBackend>(module, program, opt);
        let result = result.map(JIT::from);
        (result, warnings)
    }

    /// Invoke this function before trying to get access to "new" compiled functions.
    pub fn finalize(&mut self) {
        self.module.finalize_definitions();
    }
    /// Get compiled function, if this function doesn't exist then `None` is returned, otherwise it's address returned.
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
    /// Get compiled static data, if this data doesn't exit then `None` is returned, otherwise it's andress and size returned.
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
        let main: unsafe extern "C" fn(i32, *const *const u8) -> i32 = std::mem::transmute(main);
        // though transmute is safe, invoking this function is unsafe because we invoke C code.
        Some(main(argc, argv.as_ptr() as *const *const u8));
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    fn compile(src: &str) -> Result<Product, Error> {
        let options = Opt {
            filename: "<test-suite>".into(),
            ..Default::default()
        };
        let module = initialize_aot_module("RccAOT".to_owned());
        super::compile(module, src, &options).0.map(|x| x.finish())
    }
    fn compile_err(src: &str) -> VecDeque<CompileError> {
        match compile(src).err().unwrap() {
            Error::Source(errs) => errs,
            _ => unreachable!(),
        }
    }
    #[test]
    fn empty() {
        let mut lex_errs = compile_err("`");
        assert!(lex_errs.pop_front().unwrap().data.is_lex_err());
        assert!(lex_errs.is_empty());

        let mut empty_errs = compile_err("");
        let err = empty_errs.pop_front().unwrap().data;
        assert_eq!(err, SemanticError::EmptyProgram.into());
        assert!(err.is_semantic_err());
        assert!(empty_errs.is_empty());

        let mut parse_err = compile_err("+++");
        let err = parse_err.pop_front();
        assert!(parse_err.is_empty());
        assert!(err.unwrap().data.is_syntax_err());
    }
}
