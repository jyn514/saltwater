use std::io::{BufRead, BufReader, Read};
use std::iter::IntoIterator;
use std::vec::IntoIter;

use super::data::{Location, Locatable, Token};

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
                line: 0,
                column: 0,
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
                Some(c) => {
                    self.location.column += 1;
                    Some(c)
                },
                None => {
                    let mut buf = String::new();
                    if let Err(msg) = self.reader.read_line(&mut buf) {
                        eprintln!("FATAL: failed to read line: {}", msg);
                        return None;
                    }
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
    fn parse_int(&mut self) -> Result<Token, String> {
        let mut current: i64 = 0;
        let mut err = false;
        loop {
            match self.peek() {
                Some(c) if '0' <= c && c <= '9' => {
                    self.next_char();
                    if !err {
                        match current.checked_mul(10).and_then(|current| current.checked_add(c as i64 - '0' as i64)) {
                            Some(c) => { current = c; }
                            None => { err = true; }
                        }
                    }
                },
                _ => { break; }
            }
        }
        if err {
            Err(String::from("Overflow while parsing integer literal"))
        } else {
            Ok(Token::Int(current))
        }
    }
}

impl<'a, R: Read> Iterator for Lexer<'a, R> {
    // option: whether the stream is exhausted
    // result: whether the next lexeme is an error
    type Item = Locatable<'a, Result<Token, String>>;

    fn next(&mut self) -> Option<Self::Item> {
        self.next_char().and_then(|c| {
            let location = self.location.clone();
            let data = match c {
                '+' => Ok(Token::Plus),
                '-' => Ok(Token::Minus),
                '*' => Ok(Token::Star),
                '/' => Ok(Token::Divide),
                '0'...'9' => {
                    self.unput(Some(c));
                    self.parse_int()
                }
                '\r'|'\n'|' ' => {
                    return self.next();
                },
                _ => Err(String::from("unknown token"))
            };
            Some(Self::Item {
                data: data,
                location: location,
            })
        })
    }
}
