mod utils;

use std::io::{self, BufRead};
use std::path;

extern crate env_logger;
extern crate log;
extern crate walkdir;
use log::{debug, info};

#[test]
fn run_all() -> Result<(), io::Error> {
    let _ = env_logger::try_init();
    for maybe_header_file in walkdir::WalkDir::new("tests/runner-tests").follow_links(true) {
        debug!("header_file is {:?}", &maybe_header_file);
        let header_file = maybe_header_file?;
        if header_file.file_type().is_dir() {
            debug!("skipping directory {}", header_file.path().display());
            continue;
        }
        let path = header_file.path();
        if path.extension().map_or(false, |e| e == "c") {
            run_one(path)?;
        } else {
            debug!("path is {}, skipping", path.display());
        }
    }
    Ok(())
}

fn run_one(path: &path::Path) -> Result<(), io::Error> {
    info!("testing {}", path.display());
    let program_bytes = std::process::Command::new("cpp")
        .args(&[
            "-P",
            "-undef",
            "-D__DBL_MAX__=1.797693134862315708e+308L",
            "-D__DBL_MIN__=2.225073858507201383e-308L",
            "-D__FLT_MAX__=3.402823466385288598e+38F",
            "-D__FLT_MIN__=1.175494350822287507e-38F",
            #[cfg(linux)]
            "-D__linux__",
        ])
        .arg(path.as_os_str())
        .output()
        .expect("failed to run preprocessor")
        .stdout;
    let program = std::str::from_utf8(&program_bytes).expect("program should be valid utf8");

    let mut reader = io::BufReader::new(std::fs::File::open(path)?);
    let mut first_line = String::new();
    reader.read_line(&mut first_line)?;
    let test_func = match dbg!(first_line.as_str().trim()) {
        "// compile" => utils::assert_compiles,
        "// no-main" => utils::assert_compiles_no_main,
        "// fail" => utils::assert_compile_error,
        "// succeeds" => utils::assert_succeeds,
        "// crash" => utils::assert_crash,
        line => {
            if line.starts_with("// code: ") {
                let mut split = line.split("// code: ");
                split.next();
                utils::assert_code(
                    &program,
                    split
                        .next()
                        .unwrap()
                        .parse()
                        .expect("tests should have a return code after 'code: '"),
                );
                return Ok(());
            } else if line.starts_with("// output: ") {
                // TODO: handle multiline output
                let mut split = line.split("// output: ");
                split.next();
                let expected = format!("{}\n", split.next().unwrap());
                utils::assert_output(&program, &expected);
                return Ok(());
            } else {
                // seems like a reasonable default
                utils::assert_succeeds
            }
        }
    };

    test_func(&program);
    Ok(())
}
