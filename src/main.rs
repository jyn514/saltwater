#[macro_use]
extern crate lazy_static;

mod data;
mod lex;
mod utils;

use std::env;
use std::fs::File;
use std::io::{self, Read};
use std::process;

use lex::Lexer;

fn main() {
    let args: Vec<String> = env::args().collect();
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
    for token in Lexer::new(&filename, buf.chars()) {
        println!("{:?}", token);
    }
}
