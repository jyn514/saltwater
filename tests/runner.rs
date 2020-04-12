mod utils;

use std::io::{self, BufRead};
use std::path;

extern crate env_logger;
extern crate log;
extern crate walkdir;
use log::debug;

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
    println!("testing {}", path.display());
    let program = std::fs::read_to_string(path).unwrap();
    let mut reader = io::BufReader::new(std::fs::File::open(path)?);
    let mut first_line = String::new();
    reader.read_line(&mut first_line)?;
    // remove trailing \n
    first_line.pop();
    let path = path.into();
    let test_func = match first_line.as_str() {
        "// compile" => utils::assert_compiles,
        "// no-main" => utils::assert_compiles_no_main,
        "// fail" | "// compile-fail" | "// compile-error" => utils::assert_compile_error,
        "// succeeds" => utils::assert_succeeds,
        "// crash" => utils::assert_crash,
        "// ignore" => panic!("ignored tests should have an associated issue"),
        line => {
            if line.starts_with("// code: ") {
                let code = line["// code: ".len()..]
                    .parse()
                    .expect("tests should have an integer after code:");
                utils::assert_code(&program, path, code);
                return Ok(());
            } else if line.starts_with("// errors: ") {
                let errors = line["// errors: ".len()..]
                    .parse()
                    .expect("tests should have an integer after code:");
                utils::assert_num_errs(&program, path, errors);
                return Ok(());
            } else if line.starts_with("// ignore: ") {
                let url = &line["// ignore: ".len()..];
                assert!(
                    url.starts_with("https://") || url.starts_with("http://"),
                    "ignored tests should have an associated issue"
                );
                return Ok(());
            } else if line.starts_with("// output: ") {
                return output_test(&line["// output: ".len()..], &mut reader, &program, path);
            } else {
                // seems like a reasonable default
                utils::assert_succeeds
            }
        }
    };

    test_func(&program, path);
    Ok(())
}

/// small state machine to handle 'output' syntax
/// syntax: '// output: ' expected_output
/// expected_output: '[^\n]*' | 'BEGIN: ' (comment_line* '\n' | [^\n]+) 'END'
/// comment_line: '\n// ' [^\n+]
fn output_test<B: BufRead>(
    line: &str, reader: &mut B, program: &str, path: path::PathBuf,
) -> Result<(), io::Error> {
    const BEGIN: &str = "BEGIN: ";
    const END: &str = "END";
    let tmp_str;
    let expected = match line {
        "" => "", // special case this so empty output doesn't need to use 'BEGIN: END'
        // everything between BEGIN: (...) END
        _ if line.starts_with(BEGIN) && line.ends_with(END) => {
            &line[BEGIN.len()..line.len() - END.len() - 1]
        }
        // special case initial lines that are empty
        "BEGIN:" => {
            tmp_str = state_machine(reader)?;
            &tmp_str
        }
        _ if line.starts_with(BEGIN) => {
            tmp_str = format!("{}{}", &line[BEGIN.len()..], state_machine(reader)?);
            &tmp_str
        }
        _ => {
            tmp_str = format!("{}\n", line);
            &tmp_str
        }
    };
    utils::assert_output(program, path, expected);
    Ok(())
}

fn state_machine<B: BufRead>(reader: &mut B) -> Result<String, io::Error> {
    const COMMENT: &str = "// ";
    let mut expected_out = String::new();
    for line in reader.lines() {
        let line = dbg!(line?);
        if line == "// END" {
            break;
        } else if !line.starts_with(COMMENT) {
            println!("warning: test runner: invalid syntax in program comment, expected `// <output>` or `// END`");
            break;
        }
        expected_out.push_str(&line[COMMENT.len()..]);
        expected_out.push('\n');
    }
    Ok(expected_out)
}
