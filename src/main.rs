#[macro_use]
extern crate lazy_static;

mod data;
mod lex;

use std::io::{self, Read};

use lex::Lexer;

fn main() {
    let mut buf = String::new();
    io::stdin().read_to_string(&mut buf).expect("I/O error reading stdin");
    for token in Lexer::new("<stdin>", buf) {
        println!("{:?}", token);
    }
}
