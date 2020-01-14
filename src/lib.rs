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
use std::path::Path;
use std::process::Command;

use cranelift_module::Backend;
use cranelift_object::ObjectBackend;

pub type Product = <ObjectBackend as Backend>::Product;

use data::prelude::CompileError;
pub use data::prelude::*;
pub use lex::Lexer;
pub use parse::Parser;

#[macro_use]
pub mod utils;
pub mod arch;
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

/// Compile and return the declarations and warnings.
pub fn compile(
    buf: &str,
    filename: String,
    debug_lex: bool,
    debug_ast: bool,
    debug_ir: bool,
) -> (Result<Product, Error>, VecDeque<CompileWarning>) {
    let mut lexer = Lexer::new(filename, buf.chars(), debug_lex);
    let (first, mut errs) = lexer.first_token();

    let first = match first {
        Some(token) => token,
        None => {
            if errs.is_empty() {
                errs.push_back(CompileError::new(
                    SemanticError::EmptyProgram.into(),
                    lexer.location(),
                ));
            }
            return (Err(Error::Source(errs)), Default::default());
        }
    };

    let mut parser = Parser::new(first, &mut lexer, debug_ast);
    let (hir, parse_errors) = parser.collect_results();
    errs.extend(parse_errors.into_iter());
    if hir.is_empty() && errs.is_empty() {
        errs.push_back(CompileError::new(
            SemanticError::EmptyProgram.into(),
            parser.location(),
        ));
    }

    let warnings = parser.warnings();
    if !errs.is_empty() {
        (Err(Error::Source(errs)), warnings)
    } else {
        (ir::compile(hir, debug_ir).map_err(Error::from), warnings)
    }
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

#[cfg(test)]
mod tests {
    use super::*;
    fn compile(src: &str) -> Result<Product, Error> {
        super::compile(src, "<test-suite>".to_owned(), false, false, false).0
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
