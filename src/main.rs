#[macro_use]
extern crate lazy_static;

mod data;
mod lex;
mod parse;
mod utils;

use std::env;
use std::fs::File;
use std::io::{self, Read};
use std::process;

use utils::error;
use lex::Lexer;
use parse::Parser;

fn main() {
    let args: Vec<String> = env::args().collect();
    // NOTE: only holds valid UTF-8, and will throw an error on invalid input
    let mut buf = String::new();
    let filename = if args.len() > 1 {
        let filename = &args[1];
        File::open(filename)
            .and_then(|mut file| file.read_to_string(&mut buf))
            .unwrap_or_else(|err| {
                eprintln!("Failed to open {}: {}", args[1], err);
                process::exit(1);
            });
        filename
    } else {
        io::stdin().read_to_string(&mut buf).unwrap_or_else(|err| {
            eprintln!("Failed to read stdin: {}", err);
            process::exit(1);
        });
        "<stdin>"
    };
    let compiler = Parser::new(Lexer::new(&filename, buf.chars()));
    for stmt in compiler {
        match stmt.data {
            Ok(s) => println!("{:?}", s),
            Err(err) => error(&err, &stmt.location)
        }
    }
}
