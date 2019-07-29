#[cfg(feature = "better_parsing")]
extern crate structopt;
#[cfg(feature = "better_parsing")]
use structopt::StructOpt;

use std::fs::File;
use std::io::{self, Read};
use std::path::PathBuf;
use std::process;
#[cfg(not(feature = "better_parsing"))]
use std::{env, ffi::OsString};

extern crate compiler;
use compiler::{compile_and_assemble, utils, CompileError};

#[cfg_attr(feature = "better_parsing", derive(StructOpt, Debug))]
struct Opt {
    /// The file to read C source from.
    ///
    /// "-" means stdin (use ./- to read a file called '-').
    /// Only one file at a time is currently accepted.
    #[cfg_attr(
        feature = "better_parsing",
        structopt(name = "FILE", default_value = "-", parse(from_os_str))
    )]
    filename: PathBuf,
    /// If set, print all tokens found by the lexer in addition to compiling.
    #[cfg_attr(feature = "better_parsing", structopt(short = "d", long = "debug-lex"))]
    debug_lex: bool,
    /// The output file to use. Defaults to 'a.out'.
    #[cfg_attr(
        feature = "better_parsing",
        structopt(short = "o", long = "output", default_value = "-", parse(from_os_str))
    )]
    output: PathBuf,
}

fn main() {
    #[cfg(feature = "better_parsing")]
    let opt = Opt::from_args();
    #[cfg(not(feature = "better_parsing"))]
    let opt = {
        let mut args = env::args_os();
        args.next();
        let first = args.next().unwrap_or_else(|| OsString::from("-"));
        let debug = first.to_string_lossy() == "-d";
        let filename = if debug {
            PathBuf::from(args.next().unwrap_or_else(|| OsString::from("-")))
        } else {
            PathBuf::from(first)
        };
        let flag = args
            .next()
            .map_or(String::new(), |s| s.to_string_lossy().into_owned());
        let output = match flag.as_str() {
            "-o" | "--output" => args
                .next()
                .unwrap_or_else(|| panic!("missing argument to -o")),
            _ => OsString::from("a.out"),
        };
        Opt {
            filename,
            debug_lex: debug,
            output: PathBuf::from(output),
        }
    };
    // NOTE: only holds valid UTF-8; will panic otherwise
    let mut buf = String::new();
    let filename = if opt.filename == PathBuf::from("-") {
        io::stdin().read_to_string(&mut buf).unwrap_or_else(|err| {
            eprintln!("Failed to read stdin: {}", err);
            process::exit(1);
        });
        PathBuf::from("<stdin>")
    } else {
        let Opt { filename, .. } = opt;
        File::open(filename.as_path())
            .and_then(|mut file| file.read_to_string(&mut buf))
            .unwrap_or_else(|err| {
                eprintln!("Failed to read {}: {}", filename.to_string_lossy(), err);
                process::exit(1);
            });
        filename
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
    compile_and_assemble(
        buf,
        filename.to_string_lossy().to_string(),
        opt.debug_lex,
        &opt.output,
    )
    .unwrap_or_else(|err| err_exit(err));
}

fn err_exit(err: CompileError) -> ! {
    use CompileError::*;
    match err {
        Semantic(err) => {
            utils::error(&err.data, &err.location);
            let (num_warnings, num_errors) = (utils::get_warnings(), utils::get_errors());
            print_issues(num_warnings, num_errors);
            process::exit(2);
        }
        IO(err) => utils::fatal(&format!("{}", err), 3),
        Platform(err) => utils::fatal(&format!("{}", err), 4),
    }
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
