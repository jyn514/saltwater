#![allow(dead_code)]

use std::io::Error;
use std::path::Path;
use std::process::{Command, Output};

extern crate compiler;
extern crate tempfile;

use compiler::CompileError;

pub fn compile_and_run(program: String, args: &[&str]) -> Result<Output, CompileError> {
    let output = tempfile::NamedTempFile::new().unwrap().into_temp_path();
    compile(program, &output)?;
    run(&output, args).map_err(CompileError::IO)
}

pub fn compile(program: String, output: &Path) -> Result<(), CompileError> {
    compiler::compile_and_assemble(program, "<integration-test>".to_string(), false, output)
}

pub fn run(program: &Path, args: &[&str]) -> Result<Output, Error> {
    Command::new(program).args(args).output()
}

pub fn assert_compile_error(program: &str) {
    let output = tempfile::NamedTempFile::new().unwrap().into_temp_path();
    assert!(match compile(program.to_string(), &output) {
        Err(CompileError::Semantic(_)) => true,
        _ => false,
    });
}

pub fn assert_succeeds(program: &str) {
    assert!(match compile_and_run(program.to_string(), &[]) {
        Err(_) => false,
        Ok(output) => output.status.success(),
    });
}
