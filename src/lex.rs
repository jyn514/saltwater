use std::io::{BufRead, BufReader, Read};
use std::iter::IntoIterator;
use std::vec::IntoIter;

use super::data::{Location, Token, TokenType, Error};

pub struct Lexer<'a, R: Read> {
    location: Location<'a>,
    reader: BufReader<R>,
    iterator: IntoIter<char>
}

impl<'a, R: Read> Lexer<'a, R> {
    pub fn new(filename: &'a str, stream: BufReader<R>) -> Lexer<'a, R> {
        Lexer {
            location: Location {
                line: 1,
                column: 1,
                file: filename
            },
            reader: stream,
            iterator: Vec::new().into_iter()
        }
    }
    fn next_char(&mut self) -> Option<char> {
        match self.iterator.next() {
            Some(c) => Some(c),
            None => {
                let mut buf = String::new();
                self.reader.read_line(&mut buf);
                self.location.line += 1;
                self.location.column = 1;
                self.iterator = buf.chars().collect::<Vec<_>>().into_iter();
                self.iterator.next()
            }
        }
    }
}

impl<'a, R: Read> Iterator for Lexer<'a, R> {
    // option: whether the stream is exhausted
    // result: whether the next lexeme is an error
    type Item = Result<Token<'a>, Error<'a>>;

    fn next(&mut self) -> Option<Self::Item> {
        self.next_char().and_then(|c| {
            let location = self.location.clone();
            let ret = Some(match c {
                '+' => Ok(Token {
                        location: location,
                        data: TokenType::Plus
                    }),
                _ => Err(Error {
                    location: location,
                    data: String::from("unknown token")
                })
            });
            self.location.column += 1;
            ret
        })
    }
}
