#![allow(unused_variables)]
#![warn(variant_size_differences)]
#![warn(unreachable_pub)]
#![warn(deprecated_in_future)]
#![forbid(unsafe_code)]

use std::io::{self, Write};
use std::path::Path;
use std::process::Command;

#[macro_use]
extern crate lazy_static;
use cranelift_faerie::FaerieBackend;
use cranelift_module::Backend;
use failure::Error;
use tempfile::NamedTempFile;

pub type Product = <FaerieBackend as Backend>::Product;

pub use data::{Declaration, Locatable};
pub use lex::Lexer;
pub use parse::Parser;
use utils::error;

#[macro_use]
pub mod utils;
mod backend;
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

/// Bridges the gap between the Rust type system of Inkwell to the
/// C type system of LLVM
/// Also links the resulting object file using the host `cc`
pub fn compile_and_assemble(
    buf: String,
    filename: String,
    debug_lex: bool,
    output_file: &Path,
) -> Result<(), CompileError> {
    let product = compile(buf, filename.clone(), debug_lex);

    let mut tmp_file = NamedTempFile::new().expect("should be able to create temp file");

    let bytes = product?.emit().map_err(CompileError::Platform)?;
    tmp_file.write_all(&bytes).map_err(CompileError::IO)?;

    // link the .o file
    let status = Command::new("cc")
        .args(&[&tmp_file.path(), Path::new("-o"), output_file])
        .status()?;
    if !status.success() {
        Err(CompileError::IO(io::Error::new(
            io::ErrorKind::Other,
            "linking program failed",
        )))
    } else {
        Ok(())
    }
}

pub fn compile(buf: String, filename: String, debug_lex: bool) -> Result<Product, CompileError> {
    if debug_lex {
        for lexeme in Lexer::new(filename.clone(), buf.chars()) {
            match lexeme.data {
                Ok(l) => println!("{:#?}", l),
                Err(err) => error(&err, &lexeme.location),
            }
        }
    }
    let parser = Parser::new(Lexer::new(filename, buf.chars()));
    let hir = parser.collect::<Result<Vec<Locatable<Declaration>>, Locatable<String>>>();
    let hir = match hir {
        Err(err) => return Err(CompileError::Semantic(err)),
        Ok(program) => program,
    };
    ir::compile(hir)
        .map_err(CompileError::Semantic)
        .map(|product| product.finish())
}
