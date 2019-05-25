use lazy_static;

use core::f64::{INFINITY, NEG_INFINITY};
use std::collections::HashMap;
use std::convert::TryFrom;
use std::str::Chars;

use super::data::{Keyword, Locatable, Location, Token};
use super::utils::warn;

#[derive(Debug)]
pub struct Lexer<'a> {
    location: Location<'a>,
    chars: Chars<'a>,
    current: Option<char>,
}

enum CharError {
    Eof,
    Newline,
    Terminator,
}

lazy_static! {
    static ref KEYWORDS: HashMap<&'static str, Keyword> = {
        let mut m = HashMap::new();

        // booleans
        //m.insert("false", Token::False);
        //m.insert("true", Token::True);

        // control flow
        m.insert("if", Keyword::If);
        m.insert("else", Keyword::Else);
        m.insert("do", Keyword::Do);
        m.insert("while", Keyword::While);
        m.insert("for", Keyword::For);
        m.insert("switch", Keyword::Switch);
        m.insert("case", Keyword::Case);
        m.insert("default", Keyword::Default);
        m.insert("break", Keyword::Break);
        m.insert("continue", Keyword::Continue);
        m.insert("return", Keyword::Return);
        m.insert("goto", Keyword::Goto);

        // types
        m.insert("bool", Keyword::Bool);
        m.insert("char", Keyword::Char);
        m.insert("short", Keyword::Short);
        m.insert("int", Keyword::Int);
        m.insert("long", Keyword::Long);
        m.insert("float", Keyword::Float);
        m.insert("double", Keyword::Double);
        m.insert("void", Keyword::Void);
        m.insert("signed", Keyword::Signed);
        m.insert("unsigned", Keyword::Unsigned);
        m.insert("typedef", Keyword::Typedef);
        m.insert("union", Keyword::Union);
        m.insert("struct", Keyword::Struct);

        // qualifiers
        m.insert("const", Keyword::Const);
        m.insert("volatile", Keyword::Volatile);

        // storage classes
        m.insert("auto", Keyword::Auto);
        m.insert("register", Keyword::Register);
        m.insert("static", Keyword::Static);
        m.insert("extern", Keyword::Extern);

        m.insert("sizeof", Keyword::Sizeof);
        m
    };
}

impl<'a> Lexer<'a> {
    pub fn new(filename: &'a str, chars: Chars<'a>) -> Lexer<'a> {
        Lexer {
            location: Location {
                line: 1,
                column: 0,
                file: filename,
            },
            chars,
            current: None,
        }
    }
    fn next_char(&mut self) -> Option<char> {
        if let Some(c) = self.current {
            self.current = None;
            Some(c)
        } else {
            self.chars.next().map(|x| {
                if x == '\n' {
                    self.location.line += 1;
                    self.location.column = 1;
                    x
                } else {
                    self.location.column += 1;
                    x
                }
            })
        }
    }
    fn unput(&mut self, c: Option<char>) {
        self.current = c;
    }
    fn peek(&mut self) -> Option<char> {
        self.current = self.next_char();
        self.current
    }
    fn consume_whitespace(&mut self) {
        while self.peek().map_or(false, |c| c.is_ascii_whitespace()) {
            self.next_char();
        }
    }
    fn consume_line_comment(&mut self) {
        while let Some(c) = self.next_char() {
            if c == '\n' {
                break;
            }
        }
    }
    fn consume_multi_comment(&mut self) {
        while let Some(c) = self.next_char() {
            if c == '*' && self.peek() == Some('/') {
                self.next_char();
                break;
            }
        }
    }
    fn parse_num(&mut self, start: char, first_run: bool) -> Result<Token, String> {
        // we keep going on error so we don't get more errors from unconsumed input
        let mut err = false;
        let negative = start == '-';

        // the radix check is funky, it's easier to just make the first character part of
        // the number proper (instead of '-')
        let start = if negative {
            self.next_char()
                .expect("main loop should ensure '-' is followed by digit if passed to parse_num")
        } else {
            start
        };

        if start == '.' {
            return self.parse_float(0, 10, negative);
        }
        let mut current = start as i64 - '0' as i64;

        // check for radix other than 10 - but if we see '.', use 10
        let radix = if start == '0' {
            match self.peek() {
                Some('b') => {
                    self.next_char();
                    2
                }
                Some('x') => {
                    self.next_char();
                    16
                }
                // float: 0.431
                Some('.') => 10,
                _ => 8,
            }
        } else {
            10
        };

        // main loop
        while let Some(c) = self.next_char() {
            if c == '.' {
                if first_run {
                    return self.parse_float(current, radix, negative);
                } else {
                    return Err(String::from("exponents cannot be floating point numbers"));
                }
            } else if !c.is_digit(radix) {
                self.unput(Some(c));
                break;
            }
            if !err {
                match current
                    .checked_mul(i64::from(radix))
                    .and_then(|current| current.checked_add(c as i64 - '0' as i64))
                {
                    Some(c) => {
                        current = c;
                    }
                    None => {
                        err = true;
                    }
                }
            }
        }
        if err {
            return Err(String::from("overflow while parsing integer literal"));
        }
        if negative {
            current = -current;
        }
        if first_run {
            let exp = self.parse_exponent()?;
            if exp.is_negative() {
                // this may truncate
                // TODO: conversion to f64 might lose precision? need to check
                Ok(Token::Int((10_f64.powi(exp) * current as f64) as i64))
            } else {
                match 10_i64
                    .checked_pow(exp as u32)
                    .and_then(|p| p.checked_mul(current))
                {
                    Some(i) => Ok(Token::Int(i)),
                    None => Err(String::from("overflow while parsing integer literal")),
                }
            }
        } else {
            Ok(Token::Int(current))
        }
    }
    // at this point we've already seen a '.', if we see one again it's an error
    fn parse_float(&mut self, start: i64, radix: u32, negative: bool) -> Result<Token, String> {
        let radix_f = f64::from(radix);
        let (mut fraction, mut current_base): (f64, f64) = (0.0, 1.0 / radix_f);
        // parse fraction
        while let Some(c) = self.peek() {
            if c.is_digit(radix) && current_base != 0.0 {
                self.next_char();
                fraction += (c as i64 - '0' as i64) as f64 * current_base;
                current_base /= radix_f;
            } else {
                break;
            }
        }
        let result = 10_f64.powi(self.parse_exponent()?) * (start as f64 + fraction);
        if result == INFINITY || result == NEG_INFINITY {
            Err(String::from(
                "overflow error while parsing floating literal",
            ))
        } else {
            Ok(Token::Float(if negative { -result } else { result }))
        }
    }
    // should only be called at the end of a number. mostly error handling
    fn parse_exponent(&mut self) -> Result<i32, String> {
        if !(self.peek() == Some('e') || self.peek() == Some('E')) {
            return Ok(0);
        }
        self.next_char();
        let next = self.peek();
        if !(next.is_some() && (next.unwrap().is_ascii_digit() || next == Some('-'))) {
            return Err(String::from("exponent for floating literal has no digits"));
        }
        let next = self.next_char().unwrap();
        match self.parse_num(next, false)? {
            Token::Int(i) => i32::try_from(i).map_err(|_| {
                "only 32-bit exponents are allowed, 64-bit exponents will overflow".to_string()
            }),
            _ => panic!(
                "parse_num should never return something besides Token::Int \
                 when called with first_run: false"
            ),
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
                        _ => {
                            warn(
                                &format!("unknown character escape '\\{}'", c),
                                &self.location,
                            );
                            c
                        }
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
        let (term_err, newline_err) = (
            Err(String::from(
                "Missing terminating ' character in char literal",
            )),
            Err(String::from("Illegal newline while parsing char literal")),
        );
        match self.parse_single_char(false) {
            Ok(c) => match self.next_char() {
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
                }
            },
            Err(CharError::Eof) => term_err,
            Err(CharError::Newline) => newline_err,
            Err(CharError::Terminator) => Err(String::from("Empty character constant")),
        }
    }
    fn parse_string(&mut self) -> Result<Token, String> {
        let mut literal = String::new();
        // allow multiple adjacent strings
        while self.peek() == Some('"') {
            self.next_char(); // start quote
            loop {
                match self.parse_single_char(true) {
                    Ok(c) => literal.push(c),
                    Err(CharError::Eof) => {
                        return Err(String::from(
                            "Missing terminating \" character in string literal",
                        ))
                    }
                    Err(CharError::Newline) => {
                        return Err(String::from("Illegal newline while parsing string literal"))
                    }
                    Err(CharError::Terminator) => break,
                }
            }
            self.consume_whitespace();
        }
        literal.push('\0');
        Ok(Token::Str(literal))
    }
    fn parse_id(&mut self, start: char) -> Result<Token, String> {
        let mut id = String::new();
        id.push(start);
        while let Some(c) = self.next_char() {
            if c.is_digit(10) || 'a' <= c && c <= 'z' || 'A' <= c && c <= 'Z' || c == '_' {
                id.push(c);
            } else {
                self.unput(Some(c));
                break;
            }
        }
        match KEYWORDS.get::<str>(&id) {
            Some(keyword) => Ok(Token::Keyword(*keyword)),
            None => Ok(Token::Id(id)),
        }
    }
}

impl<'a> Iterator for Lexer<'a> {
    // option: whether the stream is exhausted
    // result: whether the next lexeme is an error
    type Item = Locatable<'a, Result<Token, String>>;

    fn next(&mut self) -> Option<Self::Item> {
        self.consume_whitespace();
        self.next_char().and_then(|c| {
            let location = self.location.clone();
            let data = match c {
                '+' => Ok(match self.peek() {
                    Some('=') => {
                        self.next_char();
                        Token::PlusEqual
                    }
                    Some('+') => {
                        self.next_char();
                        Token::PlusPlus
                    }
                    _ => Token::Plus,
                }),
                '-' => match self.peek() {
                    Some('=') => {
                        self.next_char();
                        Ok(Token::MinusEqual)
                    }
                    Some('-') => {
                        self.next_char();
                        Ok(Token::MinusMinus)
                    }
                    // we have to parse - as part of number so that we can have
                    // negative exponents after floats
                    Some(c) if c.is_ascii_digit() => self.parse_num('-', true),
                    c => {
                        self.unput(c);
                        Ok(Token::Minus)
                    }
                },
                '*' => Ok(Token::Star),
                '/' => match self.next_char() {
                    Some('/') => {
                        self.consume_line_comment();
                        return self.next();
                    }
                    Some('*') => {
                        self.consume_multi_comment();
                        return self.next();
                    }
                    Some('=') => Ok(Token::DivideEqual),
                    c => {
                        self.unput(c);
                        Ok(Token::Divide)
                    }
                },
                '%' => Ok(Token::Mod),
                '=' => Ok(match self.peek() {
                    Some('=') => {
                        self.next_char();
                        Token::EqualEqual
                    }
                    _ => Token::Equal,
                }),
                '!' => Ok(match self.peek() {
                    Some('=') => {
                        self.next_char();
                        Token::NotEqual
                    }
                    _ => Token::Not,
                }),
                '>' => Ok(match self.peek() {
                    Some('=') => {
                        self.next_char();
                        Token::GreaterEqual
                    }
                    Some('>') => {
                        self.next_char();
                        Token::ShiftRight
                    }
                    _ => Token::Greater,
                }),
                '<' => Ok(match self.peek() {
                    Some('=') => {
                        self.next_char();
                        Token::LessEqual
                    }
                    Some('<') => {
                        self.next_char();
                        Token::ShiftLeft
                    }
                    _ => Token::Less,
                }),
                '&' => Ok(match self.peek() {
                    Some('&') => {
                        self.next_char();
                        Token::LogicalAnd
                    }
                    _ => Token::Ampersand,
                }),
                '|' => Ok(match self.peek() {
                    Some('|') => {
                        self.next_char();
                        Token::LogicalOr
                    }
                    _ => Token::BinaryOr,
                }),
                '{' => Ok(Token::LeftBrace),
                '}' => Ok(Token::RightBrace),
                '(' => Ok(Token::LeftParen),
                ')' => Ok(Token::RightParen),
                ';' => Ok(Token::Semicolon),
                ':' => Ok(Token::Colon),
                '[' => Ok(Token::LeftBracket),
                ']' => Ok(Token::RightBracket),
                ',' => Ok(Token::Comma),
                '.' => match self.peek() {
                    Some(c) if c.is_ascii_digit() => self.parse_num('.', true),
                    _ => Ok(Token::Dot),
                },
                '?' => Ok(Token::Question),
                '0'...'9' => self.parse_num(c, true),
                'a'...'z' | 'A'...'Z' | '_' => self.parse_id(c),
                '\'' => self.parse_char(),
                '"' => {
                    self.unput(Some('"'));
                    self.parse_string()
                }
                _ => Err(String::from("unknown token")),
            };
            Some(Self::Item { data, location })
        })
    }
}

#[cfg(test)]
mod tests {
    use super::{Lexer, Locatable, Location, Token};

    type LexType<'a> = Locatable<'a, Result<Token, String>>;

    fn lex<'a>(input: &'a str) -> Option<LexType<'a>> {
        lex_all(input).get(0).map(|x| x.clone())
    }
    fn lex_all<'a>(input: &'a str) -> Vec<LexType<'a>> {
        Lexer::new("<stdin>", input.chars()).collect()
    }

    fn match_data<'a, T>(lexed: Option<LexType<'a>>, closure: T) -> bool
    where
        T: Fn(Result<Token, String>) -> bool,
    {
        match lexed {
            Some(result) => closure(result.data),
            None => false,
        }
    }

    #[test]
    fn test_plus() {
        let parse = lex("+");
        assert_eq!(
            parse,
            Some(Locatable {
                data: Ok(Token::Plus),
                location: Location {
                    file: "<stdin>",
                    line: 1,
                    column: 1
                }
            })
        )
    }

    #[test]
    fn test_overflow() {
        assert!(match lex("10000000000000000000000") {
            Some(lexed) => lexed.data.is_err(),
            None => false,
        })
    }

    #[test]
    fn test_num_literals() {
        assert!(match_data(lex("10"), |lexed| lexed == Ok(Token::Int(10))));
        assert!(match_data(lex("0x10"), |lexed| lexed == Ok(Token::Int(16))));
        assert!(match_data(lex("0b10"), |lexed| lexed == Ok(Token::Int(2))));
        assert!(match_data(lex("010"), |lexed| lexed == Ok(Token::Int(8))));
        assert!(match_data(lex("02"), |lexed| lexed == Ok(Token::Int(2))));
        assert!(match_data(lex("0"), |lexed| lexed == Ok(Token::Int(0))));
        assert!(match_data(lex("0.1"), |lexed| lexed == Ok(Token::Float(0.1))));
        assert!(match_data(lex(".1"), |lexed| lexed == Ok(Token::Float(0.1))));
        assert!(match_data(lex("1e10"), |lexed| lexed == Ok(Token::Int(10000000000))));
        assert!(match_data(lex("-1"), |lexed| lexed == Ok(Token::Int(-1))));
        assert!(match_data(lex("-1e10"), |lexed| lexed == Ok(Token::Int(-10000000000))));
        assert!(match_data(lex("-1.2"), |lexed| lexed == Ok(Token::Float(-1.2))));
        assert!(match_data(lex("-1.2e10"), |lexed| lexed == Ok(Token::Float(-1.2e10))));
        assert!(match_data(lex("-1.2e-1"), |lexed| lexed == Ok(Token::Float(-1.2e-1))));
        assert!(match_data(lex("1e-1"), |lexed| lexed == Ok(Token::Int(0))));
        assert!(match_data(lex("-1e-1"), |lexed| lexed == Ok(Token::Int(0))))
    }

    #[test]
    fn test_num_errors() {
        assert!(match_data(lex("1e"), |t| t.is_err()));
        assert!(match_data(lex("1e."), |t| t.is_err()));
        assert!(match_data(lex("1e1.0"), |t| t.is_err()));
        //assert!(match_data(lex("1e100000"), |t| t.is_err());
        //assert!(match_data(lex("1e-100000"), |t| t.is_err());
    }

    #[test]
    // used to have a stack overflow on large consecutive whitespace inputs
    fn test_lots_of_whitespace() {
        let mut spaces = Vec::new();
        spaces.resize(8096, '\n');
        assert!(lex(&spaces.into_iter().collect::<String>()) == None)
    }

    // Integration tests
    #[test]
    fn test_for_loop() {
        assert!(lex_all(
            "for (int i = 0; i < 100; ++i {
            a[i] = i << 2 + i*4;
            }"
        )
        .into_iter()
        .all(|x| x.data.is_ok()))
    }
}
