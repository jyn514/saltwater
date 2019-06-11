#[macro_use]
extern crate lazy_static;
extern crate structopt;

#[macro_use]
mod utils;
mod data;
mod lex;
mod parse;

use std::fs::File;
use std::io::{self, Read};
use std::process;

use structopt::StructOpt;

use lex::Lexer;
use parse::Parser;
use utils::error;

#[derive(StructOpt, Debug)]
struct Opt {
    /// The file to read C source from.
    ///
    /// "-" means stdin (use ./- to read a file called '-').
    /// Only one file at a time is currently accepted.
    #[structopt(name = "FILE", default_value = "-", parse(from_str))]
    filename: String,
    /// If set, print all tokens found by the lexer in addition to compiling.
    #[structopt(short = "d", long = "debug-lex")]
    debug_lex: bool,
}

fn main() {
    let opt = Opt::from_args();
    // NOTE: only holds valid UTF-8; will panic otherwise
    let mut buf = String::new();
    let filename = if opt.filename == "-" {
        io::stdin().read_to_string(&mut buf).unwrap_or_else(|err| {
            eprintln!("Failed to read stdin: {}", err);
            process::exit(1);
        });
        "<stdin>".to_string()
    } else {
        let Opt { filename, .. } = opt;
        File::open(&filename)
            .and_then(|mut file| file.read_to_string(&mut buf))
            .unwrap_or_else(|err| {
                eprintln!("Failed to read {}: {}", filename, err);
                process::exit(1);
            });
        filename
    };
    if opt.debug_lex {
        for lexeme in Lexer::new(filename.clone(), buf.chars()) {
            match lexeme.data {
                Ok(l) => println!("{:?}", l),
                Err(err) => error(&err, &lexeme.location),
            }
        }
    }
    let compiler = Parser::new(Lexer::new(filename, buf.chars()));
    for stmt in compiler {
        match stmt.data {
            Ok(s) => println!("{:?}", s),
            Err(err) => error(&err, &stmt.location),
        }
    }
}
