use lazy_static;

use core::f64::{INFINITY, NEG_INFINITY};
use std::collections::HashMap;
use std::convert::TryFrom;
use std::str::Chars;

use super::data::{Keyword, Locatable, Location, Token};
use super::utils::warn;

/// A Lexer takes the source code and turns it into tokens with location information.
///
/// Tokens are either literals, keywords, identifiers, or builtin operations.
/// This allows the parser to worry about fewer things at a time.
/// Location information is irritating to deal with but allows for better error messages.
/// This is the reason the filename is mandatory, so that it can be shown in errors.
/// You may also find the `warn` and `error` functions in `utils.rs` to be useful.
///
/// Lexer implements iterator, so you can loop over the tokens.
///
/// Examples:
///
/// ```
/// let lexer = Lexer::new("<stdin>".to_string(),
///                        "int main(void) { char *hello = \"hi\"; }");
/// for token in lexer {
///     assert!(token.is_ok());
/// }
/// ```
#[derive(Debug)]
pub struct Lexer<'a> {
    location: Location,
    chars: Chars<'a>,
    // used for 2-character tokens
    current: Option<char>,
    // used for 3-character tokens
    lookahead: Option<char>,
}

// returned when lexing a string literal
enum CharError {
    Eof,
    Newline,
    Terminator,
}

lazy_static! {
    static ref KEYWORDS: HashMap<&'static str, Keyword> = map!{
        // control flow
        "if" => Keyword::If,
        "else" => Keyword::Else,
        "do" => Keyword::Do,
        "while" => Keyword::While,
        "for" => Keyword::For,
        "switch" => Keyword::Switch,
        "case" => Keyword::Case,
        "default" => Keyword::Default,
        "break" => Keyword::Break,
        "continue" => Keyword::Continue,
        "return" => Keyword::Return,
        "goto" => Keyword::Goto,

        // types
        "_Bool" => Keyword::Bool,
        "char" => Keyword::Char,
        "short" => Keyword::Short,
        "int" => Keyword::Int,
        "long" => Keyword::Long,
        "float" => Keyword::Float,
        "double" => Keyword::Double,
        "void" => Keyword::Void,
        "signed" => Keyword::Signed,
        "unsigned" => Keyword::Unsigned,
        "typedef" => Keyword::Typedef,
        "union" => Keyword::Union,
        "struct" => Keyword::Struct,

        // qualifiers
        "const" => Keyword::Const,
        "volatile" => Keyword::Volatile,

        // storage classes
        "auto" => Keyword::Auto,
        "register" => Keyword::Register,
        "static" => Keyword::Static,
        "extern" => Keyword::Extern,

        // compiler intrinsics. so far, just 'sizeof'
        "sizeof" => Keyword::Sizeof
    };
}

impl<'a> Lexer<'a> {
    /// Creates a Lexer from a filename and the contents of a file
    pub fn new(filename: String, chars: Chars<'a>) -> Lexer<'a> {
        Lexer {
            location: Location {
                line: 1,
                // not 1 because we increment column _before_ returning current char
                column: 0,
                file: filename,
            },
            chars,
            current: None,
            lookahead: None,
        }
    }
    /// This lexer is somewhat unique - it reads a single character at a time,
    /// unlike most lexers which read a token at a time (e.g. string literals).
    /// This makes some things harder to do than normal, for example integer and float parsing, because
    /// we can't use the standard library - it expects you to already have the entire string.
    ///
    /// This, along with `peek` and `unput` is sort of an iterator within an iterator:
    /// that loops over `char` instead of `Token`.
    ///
    /// Returns the next token in the stream, updating internal location information.
    /// If a lookahead already exists, use that instead.
    ///
    /// All functions should use this instead of `chars` directly.
    /// Using `chars` will not update location information and may discard lookaheads.
    fn next_char(&mut self) -> Option<char> {
        if let Some(c) = self.current {
            self.current = self.lookahead.take();
            Some(c)
        } else {
            self.chars.next().map(|x| {
                if x == '\n' {
                    self.location.line += 1;
                    self.location.column = 1;
                } else {
                    self.location.column += 1;
                };
                x
            })
        }
    }
    /// Return a character to the stream.
    /// Can be called at most one time before previous characters will be discarded.
    /// Use with caution!
    ///
    /// Examples:
    /// ```
    /// let lexer = Lexer::new(String::new(), "int main(void) {}");
    /// let first = lexer.next_char();
    /// assert!(first == Some('i'));
    /// lexer.unput(first);
    /// assert!(lexer.next_char() == Some('i'));
    /// ```
    fn unput(&mut self, c: Option<char>) {
        self.current = c;
    }
    /// Return the character that would be returned by `next_char`.
    /// Can be called any number of the times and will still return the same result.
    ///
    /// Examples:
    /// ```
    /// let lexer = Lexer::new(String::new(), "int main(void) {}");
    /// assert!(lexer.peek() == Some('i'));
    /// assert!(lexer.peek() == Some('i'));
    /// assert!(lexer.peek() == Some('i'));
    /// assert!(lexer.next_char() == Some('i'));
    /// assert!(lexer.peek() == Some('n'));
    /// ```
    fn peek(&mut self) -> Option<char> {
        self.current = self.next_char();
        self.current
    }
    /// If the next character is `item`, consume it and return true.
    /// Otherwise, return false.
    ///
    /// Examples:
    /// ```
    /// let lexer = Lexer::new(String::new(), "int main(void) {}");
    /// assert!(lexer.match_next('i'));
    /// assert!(lexer.match_next('n'));
    /// assert!(lexer.next_char() == Some('t'));
    /// ```
    fn match_next(&mut self, item: char) -> bool {
        if self.peek().map_or(false, |c| c == item) {
            self.next_char();
            true
        } else {
            false
        }
    }
    /// Remove all consecutive whitespace pending in the stream.
    ///
    /// Before: chars{"    hello   "}
    /// After:  chars{"hello   "}
    fn consume_whitespace(&mut self) {
        while self.peek().map_or(false, |c| c.is_ascii_whitespace()) {
            self.next_char();
        }
    }
    /// Remove all characters between now and the next '\n' character.
    ///
    /// Before: chars{"blah `invalid tokens``\nhello // blah"}
    /// After:  chars{"hello // blah"}
    fn consume_line_comment(&mut self) {
        while let Some(c) = self.next_char() {
            if c == '\n' {
                break;
            }
        }
    }
    /// Remove a multi-line C-style comment, i.e. until the next '*/'.
    ///
    /// TODO: show an error if the file ends before the comment has been closed.
    ///
    /// Before: chars{"hello this is a lot of text */ int main(){}"}
    /// After:  chars{" int main(){}"}
    fn consume_multi_comment(&mut self) {
        while let Some(c) = self.next_char() {
            if c == '*' && self.peek() == Some('/') {
                self.next_char();
                break;
            }
        }
    }
    /// Parse a number literal, given the starting character and whether floats are allowed.
    ///
    /// A number matches the following regex:
    /// `-?({digits}\.{digits}|{digits}|\.{digits})([eE]-?{digits})?`
    /// where {digits} is the regex `([0-9]*|0x[0-9a-f]+)`
    ///
    /// NOTE: A-F is not allowed for hex digits and a-f _is_ allowed for the
    /// fractional part of the number.
    /// NOTE: Floats are not allowed for exponents.
    /// NOTE: '-' is parsed as part of the number instead of a unary operator in order to make
    /// exponents easy to parse.
    /// TODO: return an error enum instead of Strings
    ///
    /// Since most of the code is the same for integers and floats, we use the same
    /// function for both and just pass in a flag that says whether floats are allowed.
    ///
    /// I spent way too much time on this.
    fn parse_num(&mut self, start: char, allow_float: bool) -> Result<Token, String> {
        // we keep going on error so we don't get more errors from unconsumed input
        // for example, if we stopped halfway through 10000000000000000000 because of
        // overflow, we'd get a bogus Token::Int(0).
        let mut err = false;
        // the radix check is funky, it's easier to just make the first character part of
        // the number proper (instead of '-')
        let (start, negative) = if start == '-' {
            (
                self.next_char().expect(
                    "main loop should ensure '-' is followed by digit if passed to parse_num",
                ),
                true,
            )
        } else {
            (start, false)
        };

        if start == '.' {
            assert!(allow_float);
            return self.parse_float(0, 10, negative);
        }
        // start - '0' breaks for hex digits
        assert!(
            '0' as i64 <= start as i64 && start as i64 <= '9' as i64,
            "main loop should only pass [-.0-9] as start to parse_num"
        );
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
                // octal: 0755 => 493
                _ => 8,
            }
        } else {
            10
        };

        // main loop (the first {digits} in the regex)
        while let Some(c) = self.next_char() {
            if c == '.' {
                if allow_float {
                    return self.parse_float(current, radix, negative);
                } else {
                    return Err(String::from("exponents cannot be floating point numbers"));
                }
            } else if !c.is_digit(radix) {
                self.unput(Some(c));
                break;
            }
            if !err {
                // catch overflow
                match current
                    .checked_mul(i64::from(radix))
                    .and_then(|current| current.checked_add(c as i64 - '0' as i64))
                {
                    Some(c) => current = c,
                    None => err = true,
                }
            }
        }
        if err {
            return Err(String::from("overflow while parsing integer literal"));
        }
        // doing this anywhere else is just painful. that's also the reason we pass
        // `negative` to `parse_float`
        if negative {
            current = -current;
        }
        if allow_float {
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
        // parse fraction: second {digits} in regex
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
                 when called with allow_float: false"
            ),
        }
    }
    /// Read a logical character, which may be a character escape.
    ///
    /// Has a side effect: will call `warn` if it sees an invalid escape.
    ///
    /// Before: chars{"\b'"}
    /// After:  chars{"'"}
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
                        '0' => '\0',
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
    /// Parse a character literal, starting after the opening quote.
    ///
    /// Before: chars{"\0' blah"}
    /// After:  chars{" blah"}
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
    /// Parse a string literal, starting before the opening quote.
    ///
    /// Concatenates multiple adjacent literals into one string.
    /// Adds a terminating null character, even if a null character has already been found.
    ///
    /// Before: chars{"hello" "you" "it's me" mary}
    /// After:  chars{mary}
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
    /// Parse an identifier or keyword, given the starting letter.
    ///
    /// Identifiers match the following regex: `[a-zA-Z_][a-zA-Z0-9_]*`
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
    type Item = Locatable<Result<Token, String>>;

    /// Return the next token in the stream.
    ///
    /// This iterator never resumes after it is depleted,
    /// i.e. once it returns None once, it will always return None.
    ///
    /// Any item may be an error, but items will always have an associated location.
    /// The file may be empty to start, in which case the iterator will return None.
    fn next(&mut self) -> Option<Self::Item> {
        self.consume_whitespace();
        self.next_char().and_then(|c| {
            // this clone is unavoidable, we need to keep self.location
            // but we also need each token to have a location
            let location = self.location.clone();
            // this giant switch is most of the logic
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
                    // we have to parse '-' as part of number so that we can have
                    // negative exponents after floats
                    Some(c) if c.is_ascii_digit() => self.parse_num('-', true),
                    c => {
                        self.unput(c);
                        Ok(Token::Minus)
                    }
                },
                '*' => match self.peek() {
                    Some('=') => {
                        self.next_char();
                        Ok(Token::StarEqual)
                    }
                    _ => Ok(Token::Star),
                },
                '/' => match self.next_char() {
                    Some('/') => {
                        self.consume_line_comment();
                        // TODO: many consecutive comments may cause a stack overflow
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
                '%' => Ok(match self.peek() {
                    Some('=') => {
                        self.next_char();
                        Token::ModEqual
                    }
                    _ => Token::Mod,
                }),
                '^' => Ok(if self.match_next('=') {
                    Token::XorEqual
                } else {
                    Token::Xor
                }),
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
                    _ => Token::LogicalNot,
                }),
                '>' => Ok(match self.peek() {
                    Some('=') => {
                        self.next_char();
                        Token::GreaterEqual
                    }
                    Some('>') => {
                        self.next_char();
                        if self.match_next('=') {
                            Token::RightEqual
                        } else {
                            Token::ShiftRight
                        }
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
                        if self.match_next('=') {
                            Token::LeftEqual
                        } else {
                            Token::ShiftLeft
                        }
                    }
                    _ => Token::Less,
                }),
                '&' => Ok(match self.peek() {
                    Some('&') => {
                        self.next_char();
                        Token::LogicalAnd
                    }
                    Some('=') => {
                        self.next_char();
                        Token::AndEqual
                    }
                    _ => Token::Ampersand,
                }),
                '|' => Ok(match self.peek() {
                    Some('|') => {
                        self.next_char();
                        Token::LogicalOr
                    }
                    Some('=') => {
                        self.next_char();
                        Token::OrEqual
                    }
                    _ => Token::BinaryOr,
                }),
                '{' => Ok(Token::LeftBrace),
                '}' => Ok(Token::RightBrace),
                '(' => Ok(Token::LeftParen),
                ')' => Ok(Token::RightParen),
                '[' => Ok(Token::LeftBracket),
                ']' => Ok(Token::RightBracket),
                '~' => Ok(Token::BinaryNot),
                ':' => Ok(Token::Colon),
                ';' => Ok(Token::Semicolon),
                ',' => Ok(Token::Comma),
                '.' => match self.peek() {
                    Some(c) if c.is_ascii_digit() => self.parse_num('.', true),
                    Some('.') => {
                        self.next_char();
                        if self.peek() == Some('.') {
                            self.next_char();
                            Ok(Token::Ellipsis)
                        } else {
                            // backtrack two steps
                            self.current = Some('.');
                            self.lookahead = Some('.');
                            Ok(Token::Dot)
                        }
                    }
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

    type LexType = Locatable<Result<Token, String>>;

    fn lex(input: &str) -> Option<LexType> {
        lex_all(input).get(0).cloned()
    }
    fn lex_all(input: &str) -> Vec<LexType> {
        Lexer::new("<stdin>".to_string(), input.chars()).collect()
    }

    fn match_data<T>(lexed: Option<LexType>, closure: T) -> bool
    where
        T: FnOnce(Result<Token, String>) -> bool,
    {
        match lexed {
            Some(result) => closure(result.data),
            None => false,
        }
    }

    fn match_char(lexed: Option<LexType>, expected: char) -> bool {
        match_data(lexed, |c| c == Ok(Token::Char(expected)))
    }

    fn match_str(lexed: Option<LexType>, expected: &str) -> bool {
        let mut string = expected.to_string();
        string.push('\0');
        match_data(lexed, |c| c == Ok(Token::Str(string)))
    }

    fn match_all(lexed: &[LexType], expected: &[Token]) -> bool {
        lexed
            .into_iter()
            .zip(expected)
            .all(|(actual, expected)| match &actual.data {
                Ok(token) => token == expected,
                _ => false,
            })
    }

    #[test]
    fn test_plus() {
        let parse = lex("+");
        assert_eq!(
            parse,
            Some(Locatable {
                data: Ok(Token::Plus),
                location: Location {
                    file: "<stdin>".to_string(),
                    line: 1,
                    column: 1
                }
            })
        )
    }

    #[test]
    fn test_ellipses() {
        assert!(match_all(
            &lex_all("...;...;.."),
            &[
                Token::Ellipsis,
                Token::Semicolon,
                Token::Ellipsis,
                Token::Semicolon,
                Token::Dot,
                Token::Dot,
            ]
        ));
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
    #[test]
    fn test_comments() {
        assert!(lex("/* this is a comment /* /* /* */").is_none());
        assert!(lex("// this is a comment // /// // ").is_none());
        assert!(
            lex_all(
                "/* make sure it finds things _after_ comments */
        int i;"
            )
            .len()
                == 3
        );
    }
    #[test]
    fn test_characters() {
        assert!(match_char(lex("'a'"), 'a'));
        assert!(match_char(lex("'0'"), '0'));
        assert!(match_char(lex("'\\0'"), '\0'));
        assert!(match_char(lex("'\\\\'"), '\\'));
        assert!(match_char(lex("'\\n'"), '\n'));
        assert!(match_char(lex("'\\r'"), '\r'));
        assert!(match_char(lex("'\\\"'"), '"'));
        assert!(match_char(lex("'\\''"), '\''));
        assert!(match_char(lex("'\\b'"), '\x08'));
        assert!(match_char(lex("'\\f'"), '\x0c'));
        assert!(match_char(lex("'\\t'"), '\t'));
    }
    #[test]
    fn test_strings() {
        assert!(match_str(
            lex("\"this is a sample string\""),
            "this is a sample string"
        ));
        assert!(match_str(
            lex("\"consecutive \" \"strings\""),
            "consecutive strings"
        ));
        assert!(match_str(lex("\"string with \\0\""), "string with \0"));
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
