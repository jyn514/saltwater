#![allow(dead_code)]

use std::io::Error;
use std::path::{Path, PathBuf};
use std::process::{Command, Output};

extern crate compiler;
extern crate tempfile;

use compiler::{CompileError, Opt};

pub fn compile_and_run(program: String, args: &[&str]) -> Result<Output, CompileError> {
    let output = tempfile::NamedTempFile::new().unwrap().into_temp_path();
    compile(program, false, &output)?;
    run(&output, args).map_err(CompileError::IO)
}

pub fn compile(program: String, no_link: bool, output: &Path) -> Result<(), CompileError> {
    let opt = Opt {
        output: PathBuf::from(output),
        no_link,
        ..Opt::default()
    };
    compiler::compile_and_assemble(program, "<integration-test>".to_string(), opt)
}

pub fn run(program: &Path, args: &[&str]) -> Result<Output, Error> {
    Command::new(program).args(args).output()
}

pub fn assert_compile_error(program: &str) {
    let output = tempfile::NamedTempFile::new().unwrap().into_temp_path();
    assert!(
        match compile(program.to_string(), true, &output) {
            Err(CompileError::Semantic(_)) => true,
            _ => false,
        },
        "{} should fail to compile",
        program
    );
}

pub fn assert_succeeds(program: &str) {
    assert!(
        match compile_and_run(program.to_string(), &[]) {
            Err(_) => false,
            Ok(output) => output.status.success(),
        },
        "{} should exit successfully",
        program
    );
}

pub fn assert_code(program: &str, code: i32) {
    assert!(
        match compile_and_run(program.to_string(), &[]) {
            Err(_) => false,
            Ok(output) => output.status.code().unwrap() == code,
        },
        "{} should exit with code {}",
        program,
        code
    );
}
