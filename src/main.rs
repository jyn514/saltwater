#![allow(unused_variables)]

#[macro_use]
extern crate lazy_static;
#[cfg(feature = "better_parsing")]
extern crate structopt;
#[cfg(feature = "better_parsing")]
use structopt::StructOpt;

#[macro_use]
mod utils;
mod backend;
mod data;
mod lex;
mod mir;
mod parse;

#[cfg(not(feature = "better_parsing"))]
use std::env;
use std::fs::File;
use std::io::{self, Read};
use std::process;

use lex::Lexer;
use parse::Parser;
use utils::error;

#[cfg_attr(feature = "better_parsing", derive(StructOpt, Debug))]
struct Opt {
    /// The file to read C source from.
    ///
    /// "-" means stdin (use ./- to read a file called '-').
    /// Only one file at a time is currently accepted.
    #[cfg_attr(
        feature = "better_parsing",
        structopt(name = "FILE", default_value = "-", parse(from_str))
    )]
    filename: String,
    /// If set, print all tokens found by the lexer in addition to compiling.
    #[cfg_attr(feature = "better_parsing", structopt(short = "d", long = "debug-lex"))]
    debug_lex: bool,
}

fn main() {
    #[cfg(feature = "better_parsing")]
    let opt = Opt::from_args();
    #[cfg(not(feature = "better_parsing"))]
    let opt = {
        let mut args = env::args();
        args.next();
        let first = args.next().unwrap_or_else(|| "-".to_string());
        let debug = first == "-d";
        let filename = if debug {
            args.next().unwrap_or_else(|| "-".to_string())
        } else {
            first
        };
        Opt {
            filename,
            debug_lex: debug,
        }
    };
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
                Ok(l) => println!("{:#?}", l),
                Err(err) => error(&err, &lexeme.location),
            }
        }
    }
    let compiler = Parser::new(Lexer::new(filename, buf.chars()));
    for stmt in compiler {
        match stmt {
            Ok(s) => println!("{:#?}", s.data),
            Err(err) => error(&err.data, &err.location),
        }
    }
}
