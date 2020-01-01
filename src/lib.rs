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

pub fn compile(
    buf: &str,
    filename: String,
    debug_lex: bool,
    debug_ast: bool,
    debug_ir: bool,
) -> Result<Product, Error> {
    let mut error_handler = ErrorHandler::new();
    let lexer = Lexer::new(filename, buf.chars(), debug_lex, &mut error_handler);
    let tokens = lexer.collect::<Vec<_>>();
    let parser = Parser::new(tokens.into_iter(), debug_ast, &mut error_handler)?;
    let hir = parser.collect();
    if !error_handler.is_successful() {
        return Err(Error::Source(error_handler.into_iter().collect()));
    }
    ir::compile(hir, debug_ir).map_err(Error::from)
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
