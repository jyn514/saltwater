use parser::{Lexer, Parser};
use std::io::Read;

fn main() {
    let mut src = String::new();
    std::io::stdin().read_to_string(&mut src).unwrap();
    let mut lexer = Lexer::new((), src, false);
    let first = lexer.next().unwrap().unwrap();
    let mut parser = Parser::new(first, lexer, false);
    println!("{}", dbg!(parser.expr().unwrap()));
    /*
    for decl in parser {
        println!("{}", decl.unwrap().data);
    }
    */
}
