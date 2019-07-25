#![allow(unused_variables)]

use std::ffi::OsString;
use std::fs;
use std::io::{self, Write};
use std::path::Path;
use std::process::{self, Command, Stdio};

#[macro_use]
extern crate lazy_static;
use inkwell::module::Module;

pub use data::{Declaration, Locatable};
pub use lex::Lexer;
pub use parse::Parser;
use utils::error;

#[macro_use]
mod utils;
mod backend;
pub mod data;
mod lex;
mod llvm;
mod parse;

#[derive(Debug)]
pub enum CompileError {
    Semantic(Locatable<String>),
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
) -> Result<(), CompileError> {
    let module = compile(buf, filename.clone(), debug_lex);
    module.print_to_stderr();
    let bitcode = dbg!(module.write_bitcode_to_memory());
    let mut llc = Command::new("llc")
        .arg("-filetype=obj")
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .spawn()
        .expect("failed to run llvm assembler, do you have llvm installed?");
    {
        let stdin = llc.stdin.as_mut().unwrap();
        stdin.write_all(bitcode.as_slice())?
    }
    let output = llc.wait_with_output()?;

    let obj_filename = Path::new(&filename)
        .file_stem()
        .map(|stem| {
            let mut stem = stem.to_os_string();
            stem.push(".o");
            stem
        })
        .unwrap_or_else(|| OsString::from("a.o"));
    let mut tmp_file = std::env::temp_dir();
    tmp_file.push(obj_filename);

    fs::write(&tmp_file, output.stdout)?;
    let cc = Command::new("cc")
        .args(&[&tmp_file, Path::new("-o"), Path::new("a.out")])
        .spawn()?;
    Ok(())
}

pub fn compile(buf: String, filename: String, debug_lex: bool) -> Module {
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
        Err(err) => err_exit(err),
        Ok(program) => program,
    };
    // why a closure instead of err_exit?
    // from a conversation in discord#rust-usage:
    //
    // A ! value can be coerced into any type implicitly
    // When you take the function directly you have a value of fn(&'static str) -> ! and that can't be coerced
    // When you call it you get a value of ! which can
    // It's like &String can be coerced to &str, but it's not a subtype of it
    // Likewise a fn(T) -> &String should not be allowed to coerce to fn(T) -> &str
    //
    // What's happening here is the function has type `fn(...) -> !`,
    // but when it's called, that's coerced to `!`,
    // so the closure has type `fn(...) -> i32`
    llvm::compile(hir).unwrap_or_else(|e| err_exit(e))
}

fn err_exit(err: Locatable<String>) -> ! {
    error(&err.data, &err.location);
    let (num_warnings, num_errors) = (utils::get_warnings(), utils::get_errors());
    print_issues(num_warnings, num_errors);
    process::exit(2);
}

fn print_issues(warnings: usize, errors: usize) {
    if warnings == 0 && errors == 0 {
        return;
    }
    let warn_msg = if warnings > 1 { "warnings" } else { "warning" };
    let err_msg = if errors > 1 { "errors" } else { "error" };
    let msg = match (warnings, errors) {
        (0, _) => format!("{} {}", errors, err_msg),
        (_, 0) => format!("{} {}", warnings, warn_msg),
        (_, _) => format!("{} {} and {} {}", warnings, warn_msg, errors, err_msg),
    };
    eprintln!("{} generated", msg);
}
