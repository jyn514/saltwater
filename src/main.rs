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

use lex::Lexer;
use parse::Parser;
use utils::error;

fn main() {
    let mut args: Vec<String> = env::args().collect();
    // NOTE: only holds valid UTF-8, and will throw an error on invalid input
    let mut buf = String::new();
    let filename = if args.len() > 1 && args[1] != "-" {
        let filename = std::mem::replace(&mut args[1], "".to_string());
        File::open(&filename)
            .and_then(|mut file| file.read_to_string(&mut buf))
            .unwrap_or_else(|err| {
                eprintln!("Failed to open {}: {}", filename, err);
                process::exit(1);
            });
        filename
    } else {
        io::stdin().read_to_string(&mut buf).unwrap_or_else(|err| {
            eprintln!("Failed to read stdin: {}", err);
            process::exit(1);
        });
        "<stdin>".to_string()
    };
    if args.len() > 2 && (args[2] == "-d" || args[2] == "--debug-lex") {
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
