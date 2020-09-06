#![allow(clippy::cognitive_complexity)]
#![warn(absolute_paths_not_starting_with_crate)]
#![warn(explicit_outlives_requirements)]
#![warn(unreachable_pub)]
#![warn(deprecated_in_future)]
#![deny(unsafe_code)]
#![deny(unused_extern_crates)]

use std::collections::{HashMap, VecDeque};
use std::io;
use std::path::PathBuf;
use std::rc::Rc;

use arcstr::ArcStr;
pub use codespan;

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
    pub code: ArcStr,
    pub path: PathBuf,
}

impl AsRef<str> for Source {
    fn as_ref(&self) -> &str {
        self.code.as_ref()
    }
}

pub type Files = codespan::Files<Source>;
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

pub use analyze::{Analyzer, PureAnalyzer};
pub use data::*;
// https://github.com/rust-lang/rust/issues/64762
#[allow(unreachable_pub)]
pub use lex::{Definition, Lexer, PreProcessor, PreProcessorBuilder};
pub use parse::Parser;

#[macro_use]
mod macros;
mod analyze;
/// Architecture-specific traits and data
pub mod arch;
pub mod data;
mod fold;
pub mod intern;
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

#[derive(Clone, Default)]
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

    let mut hir = vec![];
    let mut parser = Analyzer::new(Parser::new(&mut cpp, opt.debug_ast), opt.debug_hir);
    for res in &mut parser {
        match res {
            Ok(decl) => hir.push(decl),
            Err(err) => {
                errs.push_back(err);
                if let Some(max) = opt.max_errors {
                    if errs.len() >= max.into() {
                        return Program::from_cpp(cpp, Err(errs));
                    }
                }
            }
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

impl<T: Into<ArcStr>> From<T> for Source {
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
