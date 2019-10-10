#![allow(clippy::cognitive_complexity)]
#![warn(absolute_paths_not_starting_with_crate)]
#![warn(explicit_outlives_requirements)]
#![warn(unreachable_pub)]
#![warn(deprecated_in_future)]
#![deny(unsafe_code)]

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
use failure::Error;

pub type Product = <FaerieBackend as Backend>::Product;

pub use data::{Declaration, Locatable, SemanticResult};
pub use lex::Lexer;
pub use parse::Parser;

#[macro_use]
pub mod utils;
pub mod arch;
pub mod data;
mod fold;
mod ir;
mod lex;
mod parse;

#[derive(Debug)]
pub enum CompileError {
    Semantic(Locatable<String>),
    Platform(Error),
    IO(io::Error),
}

impl From<io::Error> for CompileError {
    fn from(err: io::Error) -> CompileError {
        CompileError::IO(err)
    }
}

impl From<Locatable<String>> for CompileError {
    fn from(err: Locatable<String>) -> CompileError {
        CompileError::Semantic(err)
    }
}

pub fn compile(
    buf: String,
    filename: String,
    debug_lex: bool,
    debug_ast: bool,
    debug_ir: bool,
) -> Result<Product, CompileError> {
    let lexer = Lexer::new(filename, buf.chars(), debug_lex);
    let parser = Parser::new(lexer, debug_ast);
    let hir = parser
        .collect::<SemanticResult<Vec<Locatable<Declaration>>>>()
        .map_err(CompileError::Semantic)?;

    ir::compile(hir, debug_ir)
        .map_err(CompileError::Semantic)
        .map(Module::<FaerieBackend>::finish)
}

pub fn assemble(product: Product, output: &Path) -> Result<(), CompileError> {
    let bytes = product.emit().map_err(CompileError::Platform)?;
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
