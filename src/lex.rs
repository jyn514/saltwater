use lazy_static::lazy_static;

use std::collections::HashMap;
use std::convert::TryFrom;
use std::str::Chars;

use super::data::{lex::*, prelude::*};
use super::intern::InternedStr;
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
/// use rcc::Lexer;
/// use rcc::data::prelude::*;
///
/// let mut error_handler = ErrorHandler::new();
/// let lexer = Lexer::new("<stdin>".to_string(),
///                        "int main(void) { char *hello = \"hi\"; }".chars(),
///                         false, &mut error_handler);
/// for token in lexer {
///     assert!(token.is_ok());
/// }
/// assert!(error_handler.is_successful());
/// ```
#[derive(Debug)]
pub struct Lexer<'a> {
    location: Location,
    chars: Chars<'a>,
    // used for 2-character tokens
    current: Option<char>,
    // used for 3-character tokens
    lookahead: Option<char>,
    /// whether to print out every token as it's encountered
    pub debug: bool,
    error_handler: &'a mut ErrorHandler,
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
        "__builtin_va_list" => Keyword::VaList,
        "_Bool" => Keyword::Bool,
        "char" => Keyword::Char,
        "short" => Keyword::Short,
        "int" => Keyword::Int,
        "long" => Keyword::Long,
        "float" => Keyword::Float,
        "double" => Keyword::Double,
        "_Complex" => Keyword::Complex,
        "_Imaginary" => Keyword::Imaginary,
        "void" => Keyword::Void,
        "signed" => Keyword::Signed,
        "unsigned" => Keyword::Unsigned,
        "typedef" => Keyword::Typedef,
        "enum" => Keyword::Enum,
        "union" => Keyword::Union,
        "struct" => Keyword::Struct,

        // qualifiers
        "const" => Keyword::Const,
        "volatile" => Keyword::Volatile,
        "restrict" => Keyword::Restrict,
        "_Atomic" => Keyword::Atomic,
        "_Thread_local" => Keyword::ThreadLocal,

        // function qualifiers
        "inline" => Keyword::Inline,
        "_Noreturn" => Keyword::NoReturn,

        // storage classes
        "auto" => Keyword::Auto,
        "register" => Keyword::Register,
        "static" => Keyword::Static,
        "extern" => Keyword::Extern,

        // compiler intrinsics
        "sizeof" => Keyword::Sizeof,
        "_Alignof" => Keyword::Alignof,
        "_Alignas" => Keyword::Alignas,
        "_Generic" => Keyword::Generic,
        "_Static_assert" => Keyword::StaticAssert,
    };
}

impl<'a> Lexer<'a> {
    /// Creates a Lexer from a filename and the contents of a file
    pub fn new<T: AsRef<str> + Into<String>>(
        file: T,
        chars: Chars<'a>,
        debug: bool,
        error_handler: &'a mut ErrorHandler,
    ) -> Lexer<'a> {
        Lexer {
            location: Location {
                line: 1,
                // not 1 because we increment column _before_ returning current char
                column: 0,
                file: InternedStr::get_or_intern(file),
            },
            chars,
            current: None,
            lookahead: None,
            debug,
            error_handler,
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
    ///
    /// Example:
    /// ```
    /// use rcc::Lexer;
    /// use rcc::data::prelude::*;
    ///
    /// let mut error_handler = ErrorHandler::new();
    /// let mut lexer = Lexer::new(String::new(), "int main(void) {}".chars(), false, &mut error_handler);
    /// assert!(lexer.next_char() == Some('i'));
    /// assert!(lexer.next_char() == Some('n'));
    /// assert!(lexer.next_char() == Some('t'));
    /// assert!(lexer.next_char() == Some(' '));
    /// assert!(error_handler.is_successful());
    /// ```
    pub fn next_char(&mut self) -> Option<char> {
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
    /// use rcc::Lexer;
    /// use rcc::data::prelude::*;
    ///
    /// let mut error_handler = ErrorHandler::new();
    /// let mut lexer = Lexer::new(String::new(), "int main(void) {}".chars(), false, &mut error_handler);
    /// let first = lexer.next_char();
    /// assert!(first == Some('i'));
    /// lexer.unput(first);
    /// assert!(lexer.next_char() == Some('i'));
    /// assert!(error_handler.is_successful());
    /// ```
    pub fn unput(&mut self, c: Option<char>) {
        self.current = c;
    }
    /// Return the character that would be returned by `next_char`.
    /// Can be called any number of the times and will still return the same result.
    ///
    /// Examples:
    /// ```
    /// use rcc::Lexer;
    /// use rcc::data::prelude::*;
    ///
    /// let mut error_handler = ErrorHandler::new();
    /// let mut lexer = Lexer::new(String::new(), "int main(void) {}".chars(), false, &mut error_handler);
    /// assert!(lexer.peek() == Some('i'));
    /// assert!(lexer.peek() == Some('i'));
    /// assert!(lexer.peek() == Some('i'));
    /// assert!(lexer.next_char() == Some('i'));
    /// assert!(lexer.peek() == Some('n'));
    /// assert!(error_handler.is_successful());
    /// ```
    pub fn peek(&mut self) -> Option<char> {
        self.current = self.next_char();
        self.current
    }
    /// If the next character is `item`, consume it and return true.
    /// Otherwise, return false.
    ///
    /// Examples:
    /// ```
    /// use rcc::Lexer;
    /// use rcc::data::prelude::*;
    ///
    /// let mut error_handler = ErrorHandler::new();
    /// let mut lexer = Lexer::new(String::new(), "int main(void) {}".chars(), false, &mut error_handler);
    /// assert!(lexer.match_next('i'));
    /// assert!(lexer.match_next('n'));
    /// assert!(lexer.next_char() == Some('t'));
    /// assert!(error_handler.is_successful());
    /// ```
    pub fn match_next(&mut self, item: char) -> bool {
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
    /// Before: chars{"hello this is a lot of text */ int main(){}"}
    /// After:  chars{" int main(){}"}
    fn consume_multi_comment(&mut self) -> CompileResult<()> {
        while let Some(c) = self.next_char() {
            if c == '*' && self.peek() == Some('/') {
                self.next_char();
                return Ok(());
            }
        }
        Err(CompileError {
            location: self.location,
            data: Error::UnterminatedComment,
        })
    }
    /// Parse a number literal, given the starting character and whether floats are allowed.
    ///
    /// A number matches the following regex:
    /// `({digits}\.{digits}|{digits}|\.{digits})([eE]-?{digits})?`
    /// where {digits} is the regex `([0-9]*|0x[0-9a-f]+)`
    ///
    /// TODO: return an error enum instead of Strings
    ///
    /// I spent way too much time on this.
    fn parse_num(&mut self, start: char) -> Result<Token, String> {
        // start - '0' breaks for hex digits
        assert!(
            '0' <= start && start <= '9',
            "main loop should only pass [-.0-9] as start to parse_num"
        );
        let float_literal = |f| Token::Literal(Literal::Float(f));
        let mut buf = String::new();
        buf.push(start);
        // check for radix other than 10 - but if we see '.', use 10
        let radix = if start == '0' {
            match self.next_char() {
                Some('b') => {
                    crate::utils::warn("binary number literals are an extension", self.location);
                    2
                }
                Some('x') => {
                    buf.push('x');
                    16
                }
                // float: 0.431
                Some('.') => return self.parse_float(10, buf).map(float_literal),
                // octal: 0755 => 493
                c => {
                    self.unput(c);
                    8
                }
            }
        } else {
            10
        };
        let start = start as u64 - '0' as u64;

        // the first {digits} in the regex
        let digits = match self.parse_int(start, radix, &mut buf)? {
            Some(int) => int,
            None => {
                if radix == 8 || radix == 10 || self.peek() == Some('.') {
                    start
                } else {
                    return Err(format!(
                        "missing digits to {} integer constant",
                        if radix == 2 { "binary" } else { "hexadecimal" }
                    ));
                }
            }
        };
        if self.match_next('.') {
            return self.parse_float(radix, buf).map(float_literal);
        }
        if let Some('e') | Some('E') | Some('p') | Some('P') = self.peek() {
            buf.push_str(".0"); // hexf doesn't like floats without a decimal point
            let float = self.parse_exponent(radix == 16, buf);
            self.consume_float_suffix();
            return float.map(float_literal);
        }
        let literal = if self.match_next('u') || self.match_next('U') {
            let unsigned = u64::try_from(digits)
                .map_err(|_| "overflow while parsing unsigned integer literal")?;
            Literal::UnsignedInt(unsigned)
        } else {
            let long = i64::try_from(digits)
                .map_err(|_| "overflow while parsing signed integer literal")?;
            Literal::Int(long)
        };
        // get rid of 'l' and 'll' suffixes, we don't handle them
        if self.match_next('l') {
            self.match_next('l');
        } else if self.match_next('L') {
            self.match_next('L');
        }
        Ok(Token::Literal(literal))
    }
    // at this point we've already seen a '.', if we see one again it's an error
    fn parse_float(&mut self, radix: u32, mut buf: String) -> Result<f64, String> {
        buf.push('.');
        // parse fraction: second {digits} in regex
        while let Some(c) = self.peek() {
            if c.is_digit(radix) {
                self.next_char();
                buf.push(c);
            } else {
                break;
            }
        }
        // in case of an empty mantissa, hexf doesn't like having the exponent right after the .
        // if the mantissa isn't empty, .12 is the same as .120
        //buf.push('0');
        let float = self.parse_exponent(radix == 16, buf);
        self.consume_float_suffix();
        float
    }
    fn consume_float_suffix(&mut self) {
        // Ignored for compatibility reasons
        if !(self.match_next('f') || self.match_next('F') || self.match_next('l')) {
            self.match_next('L');
        }
    }
    // should only be called at the end of a number. mostly error handling
    fn parse_exponent(&mut self, hex: bool, mut buf: String) -> Result<f64, String> {
        use std::error::Error;
        let is_digit =
            |c: Option<char>| c.map_or(false, |c| c.is_digit(10) || c == '+' || c == '-');
        if hex {
            if self.match_next('p') || self.match_next('P') {
                if !is_digit(self.peek()) {
                    return Err(String::from("exponent for floating literal has no digits"));
                }
                buf.push('p');
                buf.push(self.next_char().unwrap());
            }
        } else if self.match_next('e') || self.match_next('E') {
            if !is_digit(self.peek()) {
                return Err(String::from("exponent for floating literal has no digits"));
            }
            buf.push('e');
            buf.push(self.next_char().unwrap());
        }
        while let Some(c) = self.peek() {
            if !c.is_digit(10) {
                break;
            }
            buf.push(c);
            self.next_char();
        }
        let float = if hex {
            hexf_parse::parse_hexf64(&buf, false).map_err(|err| err.description().into())
        } else {
            buf.parse()
                .map_err(|err: std::num::ParseFloatError| err.to_string())
        }?;
        if float.is_infinite() {
            return Err("overflow parsing floating literal".into());
        }
        let should_be_zero = buf.chars().all(|c| match c {
            '.' | '+' | '-' | 'e' | 'p' | '0' => true,
            _ => false,
        });
        if float == 0.0 && !should_be_zero {
            Err("underflow parsing floating literal".into())
        } else {
            Ok(float)
        }
    }
    // returns None if there are no digits at the current position
    fn parse_int(
        &mut self,
        mut acc: u64,
        radix: u32,
        buf: &mut String,
    ) -> Result<Option<u64>, String> {
        let parse_digit = |c: char| match c.to_digit(16) {
            None => Ok(None),
            Some(digit) if digit < radix => Ok(Some(digit)),
            // if we see 'e' or 'E', it's the end of the int, don't treat it as an error
            // if we see 'b' this could be part of a binary constant (0b1)
            // if we see 'f' it could be a float suffix
            // we only get this far if it's not a valid digit for the radix, i.e. radix != 16
            Some(11) | Some(14) | Some(15) => Ok(None),
            Some(digit) => Err(format!(
                "invalid digit {} in {} constant",
                digit,
                match radix {
                    2 => "binary",
                    8 => "octal",
                    10 => "decimal",
                    16 => "hexadecimal",
                    _ => unreachable!(),
                }
            )),
        };
        // we keep going on error so we don't get more errors from unconsumed input
        // for example, if we stopped halfway through 10000000000000000000 because of
        // overflow, we'd get a bogus Token::Int(0).
        let mut err = false;
        let mut saw_digit = false;
        while let Some(c) = self.peek() {
            if err {
                self.next_char();
                continue;
            }
            let digit = match parse_digit(c)? {
                Some(d) => {
                    self.next_char();
                    saw_digit = true;
                    d
                }
                None => {
                    break;
                }
            };
            buf.push(c);
            let maybe_digits = acc
                .checked_mul(radix.into())
                .and_then(|a| a.checked_add(digit.into()));
            match maybe_digits {
                Some(digits) => acc = digits,
                None => err = true,
            }
        }
        if err {
            Err("overflow parsing integer literal".into())
        } else if !saw_digit {
            Ok(None)
        } else {
            Ok(Some(acc))
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
                        // escaped newline: "a\
                        // b"
                        '\n' => return self.parse_single_char(string),
                        'n' => '\n',   // embedded newline: "a\nb"
                        'r' => '\r',   // carriage return
                        't' => '\t',   // tab
                        '"' => '"',    // escaped "
                        '\'' => '\'',  // escaped '
                        '\\' => '\\',  // \
                        '0' => '\0',   // null character: "\0"
                        'a' => '\x07', // bell
                        'b' => '\x08', // backspace
                        'v' => '\x0b', // vertical tab
                        'f' => '\x0c', // form feed
                        '?' => '?',    // a literal '?', for trigraphs
                        _ => {
                            warn(
                                &format!("unknown character escape '\\{}'", c),
                                self.location,
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
        fn consume_until_quote(lexer: &mut Lexer) {
            loop {
                match lexer.parse_single_char(false) {
                    Ok('\'') => break,
                    Err(_) => break,
                    _ => {}
                }
            }
        }
        let (term_err, newline_err) = (
            Err(String::from(
                "Missing terminating ' character in char literal",
            )),
            Err(String::from("Illegal newline while parsing char literal")),
        );
        match self.parse_single_char(false) {
            Ok(c) if c.is_ascii() => match self.next_char() {
                Some('\'') => Ok(Literal::Char(c as u8).into()),
                Some('\n') => newline_err,
                None => term_err,
                Some(_) => {
                    consume_until_quote(self);
                    Err(String::from("Multi-character character literal"))
                }
            },
            Ok(_) => {
                consume_until_quote(self);
                Err(String::from("Multi-byte unicode character literal"))
            }
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
        Ok(Literal::Str(InternedStr::get_or_intern(literal)).into())
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
            None => Ok(Token::Id(InternedStr::get_or_intern(id))),
        }
    }
}

impl<'a> Iterator for Lexer<'a> {
    // option: whether the stream is exhausted
    // result: whether the next lexeme is an error
    type Item = CompileResult<Locatable<Token>>;

    /// Return the next token in the stream.
    ///
    /// This iterator never resumes after it is depleted,
    /// i.e. once it returns None once, it will always return None.
    ///
    /// Any item may be an error, but items will always have an associated location.
    /// The file may be empty to start, in which case the iterator will return None.
    fn next(&mut self) -> Option<Self::Item> {
        self.consume_whitespace();
        let mut c = self.next_char();
        // avoid stack overflow on lots of comments
        while c == Some('/') {
            c = match self.peek() {
                Some('/') => {
                    self.consume_line_comment();
                    self.consume_whitespace();
                    self.next_char()
                }
                Some('*') => {
                    // discard '*' so /*/ doesn't look like a complete comment
                    self.next_char();
                    if let Err(err) = self.consume_multi_comment() {
                        return Some(Err(err));
                    }
                    self.consume_whitespace();
                    self.next_char()
                }
                _ => break,
            }
        }
        let c = c.and_then(|c| {
            // this clone is unavoidable, we need to keep self.location
            // but we also need each token to have a location
            let location = self.location;
            // this giant switch is most of the logic
            let data = match c {
                '+' => match self.peek() {
                    Some('=') => {
                        self.next_char();
                        AssignmentToken::PlusEqual.into()
                    }
                    Some('+') => {
                        self.next_char();
                        Token::PlusPlus
                    }
                    _ => Token::Plus,
                },
                '-' => match self.peek() {
                    Some('=') => {
                        self.next_char();
                        AssignmentToken::MinusEqual.into()
                    }
                    Some('-') => {
                        self.next_char();
                        Token::MinusMinus
                    }
                    Some('>') => {
                        self.next_char();
                        Token::StructDeref
                    }
                    c => {
                        self.unput(c);
                        Token::Minus
                    }
                },
                '*' => match self.peek() {
                    Some('=') => {
                        self.next_char();
                        AssignmentToken::StarEqual.into()
                    }
                    _ => Token::Star,
                },
                '/' => match self.next_char() {
                    Some('=') => AssignmentToken::DivideEqual.into(),
                    c => {
                        self.unput(c);
                        Token::Divide
                    }
                },
                '%' => match self.peek() {
                    Some('=') => {
                        self.next_char();
                        AssignmentToken::ModEqual.into()
                    }
                    _ => Token::Mod,
                },
                '^' => {
                    if self.match_next('=') {
                        AssignmentToken::XorEqual.into()
                    } else {
                        Token::Xor
                    }
                }
                '=' => match self.peek() {
                    Some('=') => {
                        self.next_char();
                        ComparisonToken::EqualEqual.into()
                    }
                    _ => Token::EQUAL,
                },
                '!' => match self.peek() {
                    Some('=') => {
                        self.next_char();
                        ComparisonToken::NotEqual.into()
                    }
                    _ => Token::LogicalNot,
                },
                '>' => match self.peek() {
                    Some('=') => {
                        self.next_char();
                        ComparisonToken::GreaterEqual.into()
                    }
                    Some('>') => {
                        self.next_char();
                        if self.match_next('=') {
                            AssignmentToken::RightEqual.into()
                        } else {
                            Token::ShiftRight
                        }
                    }
                    _ => ComparisonToken::Greater.into(),
                },
                '<' => match self.peek() {
                    Some('=') => {
                        self.next_char();
                        ComparisonToken::LessEqual.into()
                    }
                    Some('<') => {
                        self.next_char();
                        if self.match_next('=') {
                            AssignmentToken::LeftEqual.into()
                        } else {
                            Token::ShiftLeft
                        }
                    }
                    _ => ComparisonToken::Less.into(),
                },
                '&' => match self.peek() {
                    Some('&') => {
                        self.next_char();
                        Token::LogicalAnd
                    }
                    Some('=') => {
                        self.next_char();
                        AssignmentToken::AndEqual.into()
                    }
                    _ => Token::Ampersand,
                },
                '|' => match self.peek() {
                    Some('|') => {
                        self.next_char();
                        Token::LogicalOr
                    }
                    Some('=') => {
                        self.next_char();
                        AssignmentToken::OrEqual.into()
                    }
                    _ => Token::BitwiseOr,
                },
                '{' => Token::LeftBrace,
                '}' => Token::RightBrace,
                '(' => Token::LeftParen,
                ')' => Token::RightParen,
                '[' => Token::LeftBracket,
                ']' => Token::RightBracket,
                '~' => Token::BinaryNot,
                ':' => Token::Colon,
                ';' => Token::Semicolon,
                ',' => Token::Comma,
                '.' => match self.peek() {
                    Some(c) if c.is_ascii_digit() => match self.parse_float(10, String::new()) {
                        Ok(f) => Literal::Float(f).into(),
                        Err(err) => {
                            return Some(Err(Locatable {
                                data: err,
                                location,
                            }))
                        }
                    },
                    Some('.') => {
                        self.next_char();
                        if self.peek() == Some('.') {
                            self.next_char();
                            Token::Ellipsis
                        } else {
                            // backtrack two steps
                            self.current = Some('.');
                            self.lookahead = Some('.');
                            Token::Dot
                        }
                    }
                    _ => Token::Dot,
                },
                '?' => Token::Question,
                '0'..='9' => match self.parse_num(c) {
                    Ok(num) => num,
                    Err(err) => return Some(Err(Locatable::new(err, location))),
                },
                'a'..='z' | 'A'..='Z' | '_' => match self.parse_id(c) {
                    Ok(id) => id,
                    Err(err) => return Some(Err(Locatable::new(err, location))),
                },
                '\'' => match self.parse_char() {
                    Ok(id) => id,
                    Err(err) => return Some(Err(Locatable::new(err, location))),
                },
                '"' => {
                    self.unput(Some('"'));
                    match self.parse_string() {
                        Ok(id) => id,
                        Err(err) => return Some(Err(Locatable::new(err, location))),
                    }
                }
                x => {
                    return Some(Err(Locatable {
                        data: format!("unknown token {:?}", x),
                        location,
                    }))
                }
            };
            Some(Ok(Locatable { data, location }))
        });
        if self.debug {
            println!("lexeme: {:?}", c);
        }
        // oof
        c.map(|result| result.map_err(|err| err.map(Error::GenericLex)))
    }
}

#[cfg(test)]
mod tests {
    use super::{CompileError, CompileResult, Lexer, Literal, Locatable, Location, Token};
    use crate::data::prelude::*;
    use crate::intern::InternedStr;

    type LexType = CompileResult<Locatable<Token>>;

    fn lex(input: &str) -> Option<LexType> {
        let mut lexed = lex_all(input);
        assert!(
            lexed.len() <= 1,
            "too many lexemes for {}: {:?}",
            input,
            lexed
        );
        lexed.pop()
    }
    fn lex_all(input: &str) -> Vec<LexType> {
        let mut error_handler = ErrorHandler::new();
        let results = Lexer::new(
            "<test suite>".to_string(),
            input.chars(),
            false,
            &mut error_handler,
        )
        .collect();
        assert!(error_handler.is_successful());
        results
    }

    fn match_data<T>(lexed: Option<LexType>, closure: T) -> bool
    where
        T: FnOnce(Result<&Token, &str>) -> bool,
    {
        match_data_ref(&lexed, closure)
    }
    fn match_data_ref<T>(lexed: &Option<LexType>, closure: T) -> bool
    where
        T: FnOnce(Result<&Token, &str>) -> bool,
    {
        match lexed {
            Some(Ok(result)) => closure(Ok(&result.data)),
            Some(Err(CompileError {
                data: Error::GenericLex(result),
                ..
            })) => closure(Err(&result)),
            _ => false,
        }
    }

    fn match_char(lexed: Option<LexType>, expected: u8) -> bool {
        match_data(lexed, |c| c == Ok(&Literal::Char(expected).into()))
    }

    fn match_str(lexed: Option<LexType>, expected: &str) -> bool {
        let string = InternedStr::get_or_intern(format!("{}\0", expected));
        match_data(lexed, |c| c == Ok(&Literal::Str(string).into()))
    }

    fn match_all(lexed: &[LexType], expected: &[Token]) -> bool {
        lexed
            .iter()
            .zip(expected)
            .all(|(actual, expected)| match actual {
                Ok(token) => token.data == *expected,
                _ => false,
            })
    }
    fn assert_int(s: &str, expected: i64) {
        assert!(
            match_data(lex(s), |lexed| lexed == Ok(&Literal::Int(expected).into())),
            "{} != {}",
            s,
            expected
        );
    }
    fn assert_float(s: &str, expected: f64) {
        let lexed = lex(s);
        assert!(
            match_data_ref(&lexed, |lexed| lexed
                == Ok(&Literal::Float(expected).into())),
            "({}) {:?} != {}",
            s,
            lexed,
            expected
        );
    }
    fn assert_err(s: &str) {
        let lexed = lex_all(s);
        assert!(
            lexed.iter().any(|e| e.is_err()),
            "{:?} is not an error (from {})",
            &lexed,
            s
        );
    }

    #[test]
    fn test_plus() {
        let parse = lex("+");
        assert_eq!(
            parse,
            Some(Ok(Locatable {
                data: Token::Plus,
                location: Location {
                    file: InternedStr::get_or_intern("<stdin>"),
                    line: 1,
                    column: 1
                }
            }))
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
            Some(lexed) => lexed.is_err(),
            None => false,
        })
    }

    #[test]
    fn test_int_literals() {
        assert_int("10", 10);
        assert_int("0x10", 16);
        assert_int("0b10", 2);
        assert_int("010", 8);
        assert_int("02l", 2);
        assert_int("0L", 0);
        assert_int("0xff", 255);
        assert_int("0xFF", 255);
        assert_err("0b");
        assert_err("0x");
        assert_err("09");
        assert_eq!(lex_all("1a").len(), 2);
    }
    #[test]
    fn test_float_literals() {
        assert_float("0.1", 0.1);
        assert_float(".1", 0.1);
        for i in 0..10 {
            assert_float(&format!("1{}e{}", "0".repeat(i), 10 - i), 1e10);
        }
        assert!(match_all(
            &lex_all("-1"),
            &[Token::Minus, Literal::Int(1).into()]
        ));
        assert!(match_all(
            &lex_all("-1e10"),
            &[Token::Minus, Literal::Float(10_000_000_000.0).into()]
        ));
        assert!(match_data(lex("9223372036854775807u"), |lexed| lexed
            == Ok(
                &Literal::UnsignedInt(9_223_372_036_854_775_807u64).into()
            )));
        assert_float("0x.ep0", 0.875);
        assert_float("0x.ep-0l", 0.875);
        assert_float("0xe.p-4f", 0.875);
        assert_float("0xep-4f", 0.875);
        // DBL_MAX is actually 1.79769313486231570814527423731704357e+308L
        // TODO: change this whenever https://github.com/rust-lang/rust/issues/31407 is closed
        assert_float(
            "1.797693134862315708e+308L",
            #[allow(clippy::excessive_precision)]
            1.797_693_134_862_315_730_8e+308,
        );
        assert_float("9.88131291682e-324L", 9.881_312_916_82e-324);
        // DBL_MIN is actually 2.22507385850720138309023271733240406e-308L
        assert_float("2.225073858507201383e-308L", 2.225_073_858_507_201_4e-308);
    }

    #[test]
    fn test_num_errors() {
        assert_err("1e");
        assert_err("1e.");
        assert_err("1e100000");
        assert_err("1e-100000");
        assert_eq!(lex_all("1e1.0").len(), 2);
    }

    fn lots_of(c: char) -> String {
        let mut buf = Vec::new();
        buf.resize(8096, c);
        buf.into_iter().collect()
    }

    #[test]
    // used to have a stack overflow on large consecutive whitespace inputs
    fn test_lots_of_whitespace() {
        assert_eq!(lex(&lots_of(' ')), None);
        assert_eq!(lex(&lots_of('\t')), None);
        assert_eq!(lex(&lots_of('\n')), None);
    }

    #[test]
    fn test_comments() {
        assert!(lex("/* this is a comment /* /* /* */").is_none());
        assert!(lex("// this is a comment // /// // ").is_none());
        assert!(lex("/*/ this is part of the comment */").is_none());
        assert_eq!(
            lex_all(
                "/* make sure it finds things _after_ comments */
        int i;"
            )
            .len(),
            3
        );
        let bad_comment = lex("/* unterminated comments are an error ");
        assert!(bad_comment.is_some() && bad_comment.unwrap().is_err());
        // check for stack overflow
        assert_eq!(lex(&"//".repeat(10_000)), None);
        assert_eq!(lex(&"/* */".repeat(10_000)), None);
    }
    #[test]
    fn test_characters() {
        assert!(match_char(lex("'a'"), b'a'));
        assert!(match_char(lex("'0'"), b'0'));
        assert!(match_char(lex("'\\0'"), b'\0'));
        assert!(match_char(lex("'\\\\'"), b'\\'));
        assert!(match_char(lex("'\\n'"), b'\n'));
        assert!(match_char(lex("'\\r'"), b'\r'));
        assert!(match_char(lex("'\\\"'"), b'"'));
        assert!(match_char(lex("'\\''"), b'\''));
        assert!(match_char(lex("'\\a'"), b'\x07'));
        assert!(match_char(lex("'\\b'"), b'\x08'));
        assert!(match_char(lex("'\\v'"), b'\x0b'));
        assert!(match_char(lex("'\\f'"), b'\x0c'));
        assert!(match_char(lex("'\\t'"), b'\t'));
        assert!(match_char(lex("'\\?'"), b'?'));
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
        .all(|x| x.is_ok()))
    }
}
