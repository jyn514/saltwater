#![allow(clippy::cognitive_complexity)]
#![warn(absolute_paths_not_starting_with_crate)]
#![warn(explicit_outlives_requirements)]
#![warn(unreachable_pub)]
#![warn(deprecated_in_future)]
#![deny(unsafe_code)]

use std::collections::VecDeque;
use std::fs::File;
use std::io::{self, Write};
use std::path::Path;
use std::process::Command;

#[macro_use]
extern crate lazy_static;
extern crate cranelift;
extern crate cranelift_faerie;
extern crate cranelift_module;
extern crate failure;

use cranelift_faerie::FaerieBackend;
use cranelift_module::{Backend, Module};

pub type Product = <FaerieBackend as Backend>::Product;

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
    Platform(failure::Error),
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
    let lexer = Lexer::new(filename, buf.chars(), debug_lex);
    let parser = Parser::new(lexer, debug_ast)?;
    let (mut hir, mut all_errs) = (vec![], vec_deque![]);
    for result in parser {
        match result {
            Err(err) => all_errs.push_back(err),
            Ok(decl) => hir.push(decl),
        }
    }
    if !all_errs.is_empty() {
        return Err(Error::Source(all_errs));
    }

    ir::compile(hir, debug_ir)
        .map_err(Error::from)
        .map(Module::<FaerieBackend>::finish)
}

pub fn assemble(product: Product, output: &Path) -> Result<(), Error> {
    let bytes = product.emit().map_err(Error::Platform)?;
    File::create(output)?
        .write_all(&bytes)
        .map_err(io::Error::into)
}

pub fn link(obj_file: &Path, output: &Path) -> Result<(), io::Error> {
    // link the .o file using host linker
    let status = Command::new("cc")
        .args(&[&obj_file, Path::new("-o"), output])
        .status()?;
    if !status.success() {
        Err(io::Error::new(
            io::ErrorKind::Other,
            "linking program failed",
        ))
    } else {
        Ok(())
    }
}
