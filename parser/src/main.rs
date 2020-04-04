use parser::{Analyzer, Lexer, Parser};
use std::io::Read;

fn main() {
    let mut src = String::new();
    std::io::stdin().read_to_string(&mut src).unwrap();
    let mut lexer = Lexer::new((), src, false);
    let first = lexer.next().unwrap().unwrap();
    let parser = Parser::new(first, lexer, false);
    let analyzer = Analyzer::new(parser);
    for decl in analyzer {
        match decl {
            Ok(ok) => println!("{}", ok.data),
            Err(err) => println!("{}", err.data),
        }
    }
}
