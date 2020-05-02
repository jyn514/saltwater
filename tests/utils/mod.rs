#![allow(dead_code)]

use std::path::{Path, PathBuf};
use std::process::{Command, Output};

extern crate env_logger;
extern crate log;
extern crate rcc;
extern crate tempfile;

use log::info;
use rcc::Error;
use target_lexicon::HOST;

pub fn init() {
    env_logger::builder().is_test(true).init();
}

pub fn cpp() -> std::process::Command {
    let mut cpp = std::process::Command::new("cpp");
    cpp.args(&[
        "-P",
        "-undef",
        "-D__DBL_MAX__=1.797693134862315708e+308L",
        "-D__DBL_MIN__=2.225073858507201383e-308L",
        "-D__FLT_MAX__=3.402823466385288598e+38F",
        "-D__FLT_MIN__=1.175494350822287507e-38F",
        "-D__INTPTR_TYPE__=8",
        "-D__INT32_TYPE__=4",
        #[cfg(linux)]
        "-D__linux__",
        #[cfg(target_arch = "x86_64")]
        "-D__x86_64__",
    ]);
    cpp
}

pub fn compile_and_run(program: &str, path: PathBuf, args: &[&str]) -> Result<Output, Error> {
    let output = compile(program, path, false)
        .unwrap_or_else(|err| panic!("failed to compile program '{}': {}", program, err));
    info!("running file {:?}", output);
    run(&output, args).map_err(Error::IO)
}

pub fn compile(program: &str, path: PathBuf, no_link: bool) -> Result<tempfile::TempPath, Error> {
    let opts = Default::default();
    let mut files = rcc::Files::default();
    let source = rcc::Source {
        code: String::from(program).into(),
        path,
    };
    let id = files.add("<test-suite>", source);
    let module = rcc::initialize_aot_module(program.to_owned(), HOST);
    let (result, _warnings) = rcc::compile(module, program, &opts, id, &mut files);
    let module = result?.finish();
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

pub fn assert_compiles(program: &str, path: PathBuf) {
    assert!(
        compile(program, path, true).is_err(),
        "{} failed to compile",
        program
    );
}

pub fn assert_compiles_no_main(fragment: &str, path: PathBuf) {
    let program = format!("int main() {{}}\n{}", fragment);
    assert!(
        compile(&program, path, true).is_ok(),
        "{} failed to compile",
        fragment
    );
}

pub fn assert_compile_error(program: &str, path: PathBuf) {
    assert!(
        match compile(program, path, true) {
            Err(Error::Source(_)) => true,
            _ => false,
        },
        "{} should fail to compile",
        program
    );
}

pub fn assert_crash(program: &str, path: PathBuf) {
    let output = compile(program, path, false).expect("could not compile program");
    log::debug!("running compiled program at {:?}", output);
    let path: &Path = output.as_ref();
    let mut handle = Command::new(path)
        .spawn()
        .expect("could not start compiled program");
    #[cfg(unix)]
    {
        use std::os::unix::process::ExitStatusExt;
        assert!(handle
            .wait()
            .expect("call to libc::wait should succeed")
            .signal()
            .is_some());
    }
    #[cfg(not(unix))]
    {
        use log::warn;
        warn!("testing for segfaults is not supported on non-unix platforms, this just checks the return code is non-zero");
        assert!(!handle.wait().unwrap().success());
    }
}

pub fn assert_output(program: &str, path: PathBuf, output: &str) {
    match compile_and_run(program, path, &[]) {
        Err(_) => panic!("program failed to compile or run: {}", program),
        Ok(actual) => assert_eq!(
            actual.stdout,
            output.as_bytes(),
            "{} should have the output {} (got {})",
            program,
            output,
            String::from_utf8_lossy(&actual.stdout),
        ),
    }
}
pub fn assert_succeeds(program: &str, path: PathBuf) {
    assert!(
        match compile_and_run(program, path, &[]) {
            Err(_) => false,
            Ok(output) => output.status.success(),
        },
        "'{}' should exit successfully",
        program
    );
}

pub fn assert_code(program: &str, path: PathBuf, code: i32) {
    assert!(
        match compile_and_run(program, path, &[]) {
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

pub fn assert_num_errs<S: AsRef<str>>(program: S, path: PathBuf, n: usize) {
    match compile(program.as_ref(), path, true) {
        Err(Error::Source(errs)) => assert!(errs.len() == n),
        _ => panic!("program should have an error"),
    }
}
