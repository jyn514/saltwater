use std::io::{BufRead, BufReader, Read};
use std::iter::IntoIterator;
use std::vec::IntoIter;

use super::data::{Location, Token, TokenType, Error};

pub struct Lexer<'a, R: Read> {
    location: Location<'a>,
    reader: BufReader<R>,
    iterator: IntoIter<char>,
    current: Option<char>
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
            iterator: Vec::new().into_iter(),
            current: None
        }
    }
    fn next_char(&mut self) -> Option<char> {
        if let Some(c) = self.current {
            self.current = None;
            Some(c)
        } else {
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
    fn unput(&mut self, c: Option<char>) {
        self.current = c;
    }
    fn peek(&mut self) -> Option<char> {
        self.current = self.next_char();
        self.current
    }
    fn parse_int(&mut self, current: i64) -> TokenType {
        match self.peek() {
            Some(c) if '0' <= c && c <= '9' => {
                self.next_char();
                self.parse_int(current*10 + c as i64 - '0' as i64)
            },
            _ => {
                TokenType::Int(current)
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
            self.location.column += 1;
            Some(Ok(Token {
                data: match c {
                    '+' => TokenType::Plus,
                    '-' => TokenType::Minus,
                    '*' => TokenType::Star,
                    '/' => TokenType::Divide,
                    '0'...'9' => {
                        self.unput(Some(c));
                        self.parse_int(0)
                    }
                    '\r'|'\n'|' ' => {
                        return self.next();
                    },
                    _ => {
                        return Some(Err(Error {
                            location: location,
                            data: String::from("unknown token")
                        }));
                    }
                },
                location: location,
            }))
        })
    }
}
