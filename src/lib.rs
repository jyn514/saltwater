#![allow(unused_variables)]
#![warn(variant_size_differences)]
#![warn(unreachable_pub)]
#![warn(deprecated_in_future)]

use std::fs::File;
use std::io::{self, Write};
use std::path::Path;
use std::process::Command;

#[macro_use]
extern crate lazy_static;
extern crate cranelift_faerie;
extern crate cranelift_module;
extern crate failure;

use cranelift_faerie::FaerieBackend;
use cranelift_module::{Backend, Module};
use failure::Error;

pub type Product = <FaerieBackend as Backend>::Product;

pub use data::{Declaration, Locatable};
pub use lex::Lexer;
pub use parse::Parser;

#[macro_use]
pub mod utils;
pub mod backend;
pub mod data;
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
) -> Result<Product, CompileError> {
    let lexer = Lexer::new(filename, buf.chars(), debug_lex);
    let parser = Parser::new(lexer, debug_ast);
    let hir = parser
        .collect::<Result<Vec<Locatable<Declaration>>, Locatable<String>>>()
        .map_err(CompileError::Semantic)?;

    ir::compile(hir)
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
