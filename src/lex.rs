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

enum CharError {
    Eof,
    Newline,
    Terminator
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
    fn parse_single_char(&mut self, string: bool) -> Result<char, CharError> {
        let terminator = if string { '"' } else { '\'' };
        if let Some(c) = self.next_char() {
            if c == '\\' {
                if let Some(c) = self.next_char() {
                    Ok(match c {
                    '\n' => return self.parse_single_char(string),
                    'n' => '\n',
                    'r' => '\r',
                    't' => '\t',
                    '"' => '"',
                    '\'' => '\'',
                    '\\' => '\\',
                    '\0' => '\0',
                    'b' => '\x08',
                    'f' => '\x0c',
                    // TODO: emit a warning (how?)
                    _ => c
                    })
                } else {
                    Err(CharError::Eof)
                }
            } else if c == '\n' {
                Err(CharError::Newline)
            } else if c == terminator {
                Err(CharError::Terminator)
            } else {
                Ok(c)
            }
        } else {
            Err(CharError::Eof)
        }
    }
    fn parse_char(&mut self) -> Result<Token, String> {
        let (term_err, newline_err) = (Err(String::from("Missing terminating ' character in char literal")),
                                     Err(String::from("Illegal newline while parsing char literal")));
        match self.parse_single_char(false) {
            Ok(c) => {
                match self.next_char() {
                    Some('\'') => Ok(Token::Char(c)),
                    Some('\n') => newline_err,
                    None => term_err,
                    Some(_) => {
                        loop {
                            match self.parse_single_char(false) {
                                Ok('\'') => break,
                                Err(_) => break,
                                _ => {}
                            }
                        }
                        Err(String::from("Multi-character character literal"))
                    },
                }
            },
            Err(CharError::Eof) => term_err,
            Err(CharError::Newline) => newline_err,
            Err(CharError::Terminator) => Err(String::from("Empty character constant")),
        }
    }
    fn parse_string(&mut self) -> Result<Token, String> {
        let mut literal = String::new();
        loop {
            match self.parse_single_char(true) {
                Ok(c) => literal.push(c),
                Err(CharError::Eof) => return Err(String::from("Missing terminating \" character in string literal")),
                Err(CharError::Newline) => return Err(String::from("Illegal newline while parsing string literal")),
                Err(CharError::Terminator) => break,
            }
        }
        Ok(Token::Str(literal))
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
                '+' => Ok(match self.peek() {
                    Some('=') => { self.next_char(); Token::PlusEqual },
                    Some('+') => { self.next_char(); Token::PlusPlus },
                     _  => Token::Plus
                }),
                '-' => Ok(match self.peek() {
                    Some('=') => { self.next_char(); Token::MinusEqual },
                    Some('-') => { self.next_char(); Token::MinusMinus },
                    _ => Token::Minus
                }),
                '*' => Ok(Token::Star),
                '/' => Ok(Token::Divide),
                '=' => Ok(match self.peek() {
                    Some('=') => Token::EqualEqual,
                    _ => Token::Equal
                }),
                '0'...'9' => {
                    self.unput(Some(c));
                    self.parse_int()
                },
                '\'' => self.parse_char(),
                '"' => self.parse_string(),
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
