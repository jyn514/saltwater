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

use compiler::compile_and_assemble;

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
    compile_and_assemble(
        buf,
        filename.to_string_lossy().to_string(),
        opt.debug_lex,
        &opt.output,
    )
    .expect("compile failed");
}
