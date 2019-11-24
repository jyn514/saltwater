#![allow(dead_code)]

use std::path::Path;
use std::process::{Command, Output};

extern crate env_logger;
extern crate log;
extern crate rcc;
extern crate tempfile;

use log::info;
use rcc::Error;

pub fn init() {
    env_logger::builder().is_test(true).init();
}

pub fn compile_and_run(program: &str, args: &[&str]) -> Result<Output, Error> {
    let output = compile(program, false)?;
    info!("running file {:?}", output);
    run(&output, args).map_err(Error::IO)
}

pub fn compile(program: &str, no_link: bool) -> Result<tempfile::TempPath, Error> {
    let module = rcc::compile(
        program,
        "<integration-test>".to_string(),
        false,
        false,
        false,
    )?;
    let output = tempfile::NamedTempFile::new()
        .expect("cannot create tempfile")
        .into_temp_path();
    info!("output is {:?}", output);
    if !no_link {
        let tmp_file = tempfile::NamedTempFile::new()
            .expect("cannot create tempfile")
            .into_temp_path();
        info!("tmp_file is {:?}", tmp_file);
        rcc::assemble(module, &tmp_file)?;
        rcc::link(&tmp_file, &output)?;
    } else {
        rcc::assemble(module, &output)?;
    };
    Ok(output)
}

pub fn run(program: &Path, args: &[&str]) -> Result<Output, std::io::Error> {
    Command::new(program).args(args).output()
}

pub fn assert_compiles(program: &str) {
    assert!(
        compile(program, true).is_err(),
        "{} failed to compile",
        program
    );
}

pub fn assert_compiles_no_main(fragment: &str) {
    let program = format!("int main() {{}}\n{}", fragment);
    assert!(
        compile(&program, true).is_ok(),
        "{} failed to compile",
        fragment
    );
}

pub fn assert_compile_error(program: &str) {
    assert!(
        match compile(program, true) {
            Err(Error::Source(_)) => true,
            _ => false,
        },
        "{} should fail to compile",
        program
    );
}

pub fn assert_output(program: &str, output: &str) {
    assert!(
        match compile_and_run(program, &[]) {
            Err(_) => false,
            Ok(actual) => actual.stdout == output.as_bytes(),
        },
        "{} should have the output {}",
        program,
        output
    );
}

pub fn assert_succeeds(program: &str) {
    assert!(
        match compile_and_run(program, &[]) {
            Err(_) => false,
            Ok(output) => output.status.success(),
        },
        "{} should exit successfully",
        program
    );
}

pub fn assert_code(program: &str, code: i32) {
    assert!(
        match compile_and_run(program, &[]) {
            Err(_) => false,
            Ok(output) => match output.status.code() {
                Some(actual) => actual == code,
                None => false,
            },
        },
        "{} should exit with code {}",
        program,
        code
    );
}

pub fn assert_num_errs<S: AsRef<str>>(program: S, n: usize) {
    match compile(program.as_ref(), true) {
        Err(Error::Source(errs)) => assert!(errs.len() == n),
        _ => panic!("program should have an error"),
    }
}
