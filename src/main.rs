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
mod llvm;
mod parse;

#[cfg(not(feature = "better_parsing"))]
use std::env;
use std::fs::File;
use std::io::{self, Read};
use std::process;

use data::{Declaration, Locatable};
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
    let parser = Parser::new(Lexer::new(filename, buf.chars()));
    let hir = parser.collect::<Result<Vec<Locatable<Declaration>>, Locatable<String>>>();
    let hir = match hir {
        Err(err) => err_exit(err),
        Ok(program) => program,
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
    let module = llvm::compile(hir).unwrap_or_else(|e| err_exit(e));
}

fn err_exit(err: Locatable<String>) -> ! {
    error(&err.data, &err.location);
    let (num_warnings, num_errors) = (utils::get_warnings(), utils::get_errors());
    print_issues(num_warnings, num_errors);
    process::exit(2);
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
