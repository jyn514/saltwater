#![allow(clippy::cognitive_complexity)]
#![warn(absolute_paths_not_starting_with_crate)]
#![warn(explicit_outlives_requirements)]
#![warn(unreachable_pub)]
#![warn(deprecated_in_future)]
#![deny(unsafe_code)]
#![deny(unused_extern_crates)]

use std::collections::VecDeque;
use std::fs::File;
use std::io::{self, Write};
use std::path::{Path, PathBuf};
use std::process::Command;
use std::rc::Rc;

use codespan::FileId;
use cranelift_module::Backend;
use cranelift_object::ObjectBackend;

/// The `Source` type for `codespan::Files`.
///
/// Used to store extra metadata about the file, like the absolute filename.
///
/// NOTE: If `path` is empty (e.g. by using `my_string.into()`),
/// then the path will be relative to the _compiler_, not to the current file.
/// This is recommended only for test code and proof of concepts,
/// since it does not adhere to the C standard.
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
pub type Product = <ObjectBackend as Backend>::Product;

pub use analyze::Analyzer;
pub use data::*;
pub use lex::{Lexer, PreProcessor};
pub use parse::Parser;

#[macro_use]
mod macros;
mod analyze;
mod arch;
pub mod data;
mod fold;
pub mod intern;
mod ir;
mod lex;
mod parse;

#[derive(Debug, thiserror::Error)]
pub enum Error {
    #[error("{}", .0.iter().map(|err| err.data.to_string()).collect::<Vec<_>>().join("\n"))]
    Source(VecDeque<CompileError>),
    #[error("platform-specific error: {0}")]
    Platform(String),
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

#[derive(Debug, Default)]
pub struct Opt {
    /// If set, print all tokens found by the lexer in addition to compiling.
    pub debug_lex: bool,

    /// If set, print the parsed abstract syntax tree in addition to compiling
    pub debug_ast: bool,

    /// If set, print the intermediate representation of the program in addition to compiling
    pub debug_asm: bool,

    /// If set, compile and assemble but do not link. Object file is machine-dependent.
    pub no_link: bool,

    /// The maximum number of errors to allow before giving up.
    /// If None, allows an unlimited number of errors.
    pub max_errors: Option<std::num::NonZeroUsize>,

    /// The directories to consider as part of the search path.
    pub search_path: Vec<PathBuf>,
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
    buf: &str, opt: &Opt, file: FileId, files: &mut Files,
) -> (
    Result<VecDeque<Locatable<Token>>, VecDeque<CompileError>>,
    VecDeque<CompileWarning>,
) {
    let path = opt.search_path.iter().map(|p| p.into());
    let mut cpp = PreProcessor::new(file, buf, opt.debug_lex, path, files);

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

/// Compile and return the declarations and warnings.
pub fn compile(
    buf: &str, opt: &Opt, file: FileId, files: &mut Files,
) -> (Result<Product, Error>, VecDeque<CompileWarning>) {
    let path = opt.search_path.iter().map(|p| p.into());
    let mut cpp = PreProcessor::new(file, buf, opt.debug_lex, path, files);

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
        file,
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
    let mut parser = Analyzer::new(Parser::new(first, &mut cpp, opt.debug_ast));
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
    let name = files.name(file).to_string_lossy();
    let (result, ir_warnings) = ir::compile(hir, name.into_owned(), opt.debug_asm);
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
    fn compile(src: &str) -> Result<Product, Error> {
        let options = Opt::default();
        let mut files: Files = Default::default();
        let id = files.add("<test suite>", src.into());
        super::compile(src, &options, id, &mut files).0
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
