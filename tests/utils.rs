use std::io::Error;
use std::process::{Command, Output};

extern crate compiler;

use compiler::CompileError;

pub fn compile_and_run(program: String, args: &[&str]) -> Result<Output, CompileError> {
    compile(program)?;
    run(args).map_err(CompileError::IO)
}

pub fn compile(program: String) -> Result<(), CompileError> {
    compiler::compile_and_assemble(program, "<integration-test>".to_string(), false)
}

pub fn run(args: &[&str]) -> Result<Output, Error> {
    Command::new("./a.out").args(args).output()
}
