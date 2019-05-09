mod data;
mod lex;

use std::io::{self, BufRead, BufReader, Error, Lines, Read};
use std::str::Chars;

use lex::Lexer;

fn main() {
    let reader: BufCharReader = BufCharReader::new(BufReader::new(io::stdin()));
    for token in Lexer::new("<stdin>", &reader) {
        /*
            match line {
                Ok(line) => line.chars(),
                Err(_) => "".chars(),
            }
        })) {
        */
        println!("{:?}", token);
    }
}

struct BufCharReader<'a> {
    //lines: Lines<BufReader<R>>,
    //current_line: Option<Result<String, Error>>,
    current_iterator: &'a Iterator<Item = char>
}

impl<'a> BufCharReader<'a> {
    fn new<R: 'a + Read>(reader: BufReader<R>) -> Self {
        BufCharReader {
            current_iterator: &reader.lines().flat_map(|s| {
                s.unwrap_or(String::new()).chars()
            })
        }
        //let mut lines = reader.lines();
        /*
        let mut reader = BufCharReader {
            lines: lines,
            current_line: Some(Ok(String::new())),
            current_iterator: "".chars()
        };
        reader.current_line = reader.lines.next();
        reader.current_iterator = reader.current_line
                          .unwrap_or(Ok(String::new()))
                          .unwrap_or(String::new())
                          .chars();
        reader
        */
    }
}

impl<'a> Iterator for BufCharReader<'a> {
    type Item = char;
    fn next(&mut self) -> Option<char> {
        self.current_iterator.next()
    }
}
