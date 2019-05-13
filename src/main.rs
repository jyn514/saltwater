#[macro_use]
extern crate lazy_static;

mod data;
mod lex;

use std::io::{self, BufReader};

use lex::Lexer;

fn main() {
    for token in Lexer::new("<stdin>", BufReader::new(io::stdin())) {
        println!("{:?}", token);
    }
}
