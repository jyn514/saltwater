use std::convert::{TryFrom, TryInto};
use std::rc::Rc;

use codespan::FileId;

use super::data::{error::LexError, lex::*, *};
use super::intern::InternedStr;
use crate::get_str;

//mod cpp;
mod cpp;
#[cfg(test)]
mod tests;
pub use cpp::PreProcessor;

/// A Lexer takes the source code and turns it into tokens with location information.
///
/// Tokens are either literals, keywords, identifiers, or builtin operations.
/// This allows the parser to worry about fewer things at a time.
/// Location information is irritating to deal with but allows for better error messages.
/// This is the reason the filename is mandatory, so that it can be shown in errors.
/// You may also find the `warn` and `error` functions in `utils.rs` to be useful.
///
/// Lexer implements iterator, so you can loop over the tokens.
/// ```
#[derive(Debug)]
pub struct Lexer {
    location: SingleLocation,
    chars: Rc<str>,
    /// used for 2-character tokens
    current: Option<u8>,
    /// used for 3-character tokens
    lookahead: Option<u8>,
    /// whether we've a token on this line before or not
    /// used for preprocessing (e.g. `#line 5` is a directive
    /// but `int main() { # line 5` is not)
    seen_line_token: bool,
    line: usize,
    error_handler: ErrorHandler,
    /// Whether or not to display each token as it is processed
    debug: bool,
}

// returned when lexing a string literal
enum CharError {
    Eof,
    Newline,
    Terminator,
    OctalTooLarge,
    HexTooLarge,
}

#[derive(Debug)]
struct SingleLocation {
    offset: u32,
    file: FileId,
}

impl Lexer {
    /// Creates a Lexer from a filename and the contents of a file
    pub fn new<S: Into<Rc<str>>>(file: FileId, chars: S, debug: bool) -> Lexer {
        Lexer {
            debug,
            location: SingleLocation { offset: 0, file },
            chars: chars.into(),
            seen_line_token: false,
            line: 0,
            current: None,
            lookahead: None,
            error_handler: ErrorHandler::new(),
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
    /// This function should never set `self.location.offset` to an out-of-bounds location
    fn next_char(&mut self) -> Option<u8> {
        let mut c = self._next_char();
        // Section 5.1.1.2 phase 2: discard backslashes before newlines
        while c == Some(b'\\') && self.peek() == Some(b'\n') {
            self._next_char(); // discard \n
            self.consume_whitespace();
            c = self._next_char();
        }
        if c == Some(b'\n') {
            self.seen_line_token = false;
            self.line += 1;
        }
        c
    }
    // Internal use only, use `next_char()` instead.
    // This gets the next token from the buffer
    // and updates the current offset and relevant fields.
    fn _next_char(&mut self) -> Option<u8> {
        if let c @ Some(_) = self.current {
            self.current = self.lookahead.take();
            c
        } else {
            assert!(self.lookahead.is_none());
            self.chars
                .as_bytes()
                .get(self.location.offset as usize)
                .copied()
        }
        .map(|c| {
            self.location.offset += 1;
            c
        })
    }
    /// Return the character that would be returned by `next_char`.
    /// Can be called any number of the times and will still return the same result.
    fn peek(&mut self) -> Option<u8> {
        self.current = self.current.or_else(|| self.lookahead.take()).or_else(|| {
            self.chars
                .as_bytes()
                .get(self.location.offset as usize)
                .copied()
        });
        self.current
    }
    /// Return the character that would be returned if you called `next_char()` twice in a row.
    /// Can be called any number of the times and will still return the same result.
    fn peek_next(&mut self) -> Option<u8> {
        self.lookahead = self.lookahead.or_else(|| {
            self.chars
                .as_bytes()
                .get((self.location.offset + 1) as usize)
                .copied()
        });
        self.lookahead
    }
    /// Return a single token to the stream.
    /// Can be called at most once before running out of space to store the token.
    ///
    /// # Panics
    /// This function will panic if called twice in a row
    /// or when `self.lookahead.is_some()`.
    fn unput(&mut self, byte: u8) {
        assert!(self.lookahead.is_none());
        self.lookahead = self.current.take();
        self.current = Some(byte);
        // TODO: this is not right,
        // it will break if someone calls `span()` before consuming the newline
        self.location.offset -= 1;
    }
    /// If the next character is `item`, consume it and return true.
    /// Otherwise, return false.
    fn match_next(&mut self, item: u8) -> bool {
        if self.peek().map_or(false, |c| c == item) {
            self.next_char();
            true
        } else {
            false
        }
    }
    /// Given the start of a span as an offset,
    /// return a span lasting until the current location in the file.
    fn span(&self, start: u32) -> Location {
        Location {
            span: (start..self.location.offset).into(),
            file: self.location.file,
        }
    }
    /// Remove all consecutive whitespace pending in the stream.
    /// This includes comments.
    ///
    /// Before: b"    // some comment\n /*multi comment*/hello   "
    /// After:  b"hello   "
    fn consume_whitespace(&mut self) {
        // there may be comments following whitespace
        loop {
            // whitespace
            while self.peek().map_or(false, |c| c.is_ascii_whitespace()) {
                self.next_char();
            }
            // comments
            if self.peek() == Some(b'/') {
                match self.peek_next() {
                    Some(b'/') => self.consume_line_comment(),
                    Some(b'*') => {
                        self.next_char();
                        self.next_char();
                        if let Err(err) = self.consume_multi_comment() {
                            self.error_handler.push_back(err);
                        }
                    }
                    _ => break,
                }
            } else {
                break;
            }
        }
    }
    /// Remove all characters between now and the next b'\n' character.
    ///
    /// Before: u8s{"blah `invalid tokens``\nhello // blah"}
    /// After:  chars{"hello // blah"}
    fn consume_line_comment(&mut self) {
        while let Some(c) = self.next_char() {
            if c == b'\n' {
                break;
            }
        }
    }
    /// Remove a multi-line C-style comment, i.e. until the next '*/'.
    ///
    /// Before: u8s{"hello this is a lot of text */ int main(){}"}
    /// After:  chars{" int main(){}"}
    fn consume_multi_comment(&mut self) -> CompileResult<()> {
        let start = self.location.offset - 2;
        while let Some(c) = self.next_char() {
            if c == b'*' && self.peek() == Some(b'/') {
                self.next_char();
                return Ok(());
            }
        }
        Err(CompileError {
            location: self.span(start),
            data: LexError::UnterminatedComment.into(),
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
    fn parse_num(&mut self, start: u8) -> Result<Token, String> {
        // start - b'0' breaks for hex digits
        assert!(
            b'0' <= start && start <= b'9',
            "main loop should only pass [-.0-9] as start to parse_num"
        );
        let span_start = self.location.offset - 1; // -1 for `start`
        let float_literal = |f| Token::Literal(Literal::Float(f));
        let mut buf = String::new();
        buf.push(start as char);
        // check for radix other than 10 - but if we see b'.', use 10
        let radix = if start == b'0' {
            if self.match_next(b'b') {
                2
            } else if self.match_next(b'x') {
                buf.push('x');
                16
            } else if self.match_next(b'.') {
                // float: 0.431
                return self.parse_float(10, buf).map(float_literal);
            } else {
                // octal: 0755 => 493
                8
            }
        } else {
            10
        };
        let start = start as u64 - b'0' as u64;

        // the first {digits} in the regex
        let digits = match self.parse_int(start, radix, &mut buf)? {
            Some(int) => int,
            None => {
                if radix == 8 || radix == 10 || self.peek() == Some(b'.') {
                    start
                } else {
                    return Err(format!(
                        "missing digits to {} integer constant",
                        if radix == 2 { "binary" } else { "hexadecimal" }
                    ));
                }
            }
        };
        if self.match_next(b'.') {
            return self.parse_float(radix, buf).map(float_literal);
        }
        if let Some(b'e') | Some(b'E') | Some(b'p') | Some(b'P') = self.peek() {
            buf.push_str(".0"); // hexf doesn't like floats without a decimal point
            let float = self.parse_exponent(radix == 16, buf);
            self.consume_float_suffix();
            return float.map(float_literal);
        }
        let literal = if self.match_next(b'u') || self.match_next(b'U') {
            let unsigned = u64::try_from(digits)
                .map_err(|_| "overflow while parsing unsigned integer literal")?;
            Literal::UnsignedInt(unsigned)
        } else {
            let long = i64::try_from(digits)
                .map_err(|_| "overflow while parsing signed integer literal")?;
            Literal::Int(long)
        };
        // get rid of b'l' and 'll' suffixes, we don't handle them
        if self.match_next(b'l') {
            self.match_next(b'l');
        } else if self.match_next(b'L') {
            self.match_next(b'L');
        }
        if radix == 2 {
            let span = self.span(span_start);
            self.error_handler
                .warn("binary number literals are an extension", span);
        }
        Ok(Token::Literal(literal))
    }
    // at this point we've already seen a '.', if we see one again it's an error
    fn parse_float(&mut self, radix: u32, mut buf: String) -> Result<f64, String> {
        buf.push('.');
        // parse fraction: second {digits} in regex
        while let Some(c) = self.peek() {
            let c = c as char;
            if c.is_digit(radix) {
                self.next_char();
                buf.push(c);
            } else {
                break;
            }
        }
        // in case of an empty mantissa, hexf doesn't like having the exponent right after the .
        // if the mantissa isn't empty, .12 is the same as .120
        //buf.push(b'0');
        let float = self.parse_exponent(radix == 16, buf);
        self.consume_float_suffix();
        float
    }
    fn consume_float_suffix(&mut self) {
        // Ignored for compatibility reasons
        if !(self.match_next(b'f') || self.match_next(b'F') || self.match_next(b'l')) {
            self.match_next(b'L');
        }
    }
    // should only be called at the end of a number. mostly error handling
    fn parse_exponent(&mut self, hex: bool, mut buf: String) -> Result<f64, String> {
        let is_digit = |c: Option<u8>| {
            c.map_or(false, |c| {
                (c as char).is_digit(10) || c == b'+' || c == b'-'
            })
        };
        if hex {
            if self.match_next(b'p') || self.match_next(b'P') {
                if !is_digit(self.peek()) {
                    return Err(String::from("exponent for floating literal has no digits"));
                }
                buf.push('p');
                buf.push(self.next_char().unwrap() as char);
            }
        } else if self.match_next(b'e') || self.match_next(b'E') {
            if !is_digit(self.peek()) {
                return Err(String::from("exponent for floating literal has no digits"));
            }
            buf.push('e');
            buf.push(self.next_char().unwrap() as char);
        }
        while let Some(c) = self.peek() {
            let c = c as char;
            if !(c).is_digit(10) {
                break;
            }
            buf.push(c);
            self.next_char();
        }
        let float = if hex {
            hexf_parse::parse_hexf64(&buf, false).map_err(|err| err.to_string())
        } else {
            buf.parse()
                .map_err(|err: std::num::ParseFloatError| err.to_string())
        }?;
        if float.is_infinite() {
            return Err("overflow parsing floating literal".into());
        }
        let should_be_zero = buf.bytes().all(|c| match c {
            b'.' | b'+' | b'-' | b'e' | b'p' | b'0' => true,
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
        &mut self, mut acc: u64, radix: u32, buf: &mut String,
    ) -> Result<Option<u64>, String> {
        let parse_digit = |c: char| match c.to_digit(16) {
            None => Ok(None),
            Some(digit) if digit < radix => Ok(Some(digit)),
            // if we see b'e' or b'E', it's the end of the int, don't treat it as an error
            // if we see b'b' this could be part of a binary constant (0b1)
            // if we see b'f' it could be a float suffix
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
            let digit = match parse_digit(c as char)? {
                Some(d) => {
                    self.next_char();
                    saw_digit = true;
                    d
                }
                None => {
                    break;
                }
            };
            buf.push(c as char);
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
    /// Before: u8s{"\b'"}
    /// After:  chars{"'"}
    fn parse_single_char(&mut self, string: bool) -> Result<u8, CharError> {
        let terminator = if string { b'"' } else { b'\'' };
        if let Some(c) = self.next_char() {
            if c == b'\\' {
                if let Some(c) = self.next_char() {
                    Ok(match c {
                        // escaped newline: "a\
                        // b"
                        b'\n' => unreachable!("should be handled earlier"),
                        b'n' => b'\n',   // embedded newline: "a\nb"
                        b'r' => b'\r',   // carriage return
                        b't' => b'\t',   // tab
                        b'"' => b'"',    // escaped "
                        b'\'' => b'\'',  // escaped '
                        b'\\' => b'\\',  // \
                        b'a' => b'\x07', // bell
                        b'b' => b'\x08', // backspace
                        b'v' => b'\x0b', // vertical tab
                        b'f' => b'\x0c', // form feed
                        b'?' => b'?',    // a literal b'?', for trigraphs
                        b'0'..=b'9' => {
                            return self.parse_octal_char_escape(c).map_err(|err| {
                                // try to avoid extraneous errors, but don't try too hard
                                self.match_next(b'\'');
                                err
                            });
                        }
                        b'x' => {
                            return self.parse_hex_char_escape().map_err(|err| {
                                // try to avoid extraneous errors, but don't try too hard
                                self.match_next(b'\'');
                                err
                            });
                        }
                        _ => {
                            self.error_handler.warn(
                                &format!("unknown character escape '\\{}'", c),
                                self.span(self.location.offset - 1),
                            );
                            c
                        }
                    })
                } else {
                    Err(CharError::Eof)
                }
            } else if c == b'\n' {
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
    fn parse_octal_char_escape(&mut self, start: u8) -> Result<u8, CharError> {
        let mut base: u16 = (start - b'0').into();
        // at most 3 digits in an octal constant, `start` is the first so only 2 possible left
        for _ in 0..2 {
            match self.peek() {
                Some(c) if b'0' <= c && c < b'8' => {
                    self.next_char();
                    base <<= 3; // base *= 8
                    base += u16::from(c - b'0');
                }
                _ => break,
            }
        }
        base.try_into().map_err(|_| CharError::OctalTooLarge)
    }
    fn parse_hex_char_escape(&mut self) -> Result<u8, CharError> {
        let mut base = 0_u64;
        let mut update = |this: &mut Self, c: u8| {
            this.next_char();
            // NOTE: this can't overflow, it will just shift in a 0
            // base *= 16
            base <<= 4;
            // NOTE: because we shifted in a 0 and c < 16, this can't overflow
            base += u64::from(c);
        };
        loop {
            match self.peek() {
                Some(c) if b'0' <= c && c <= b'9' => update(self, c - b'0'),
                Some(c) if b'a' <= c && c <= b'z' => update(self, c - b'a' + 10),
                Some(c) if b'A' <= c && c <= b'Z' => update(self, c - b'A' + 10),
                _ => break,
            }
        }
        base.try_into().map_err(|_| CharError::HexTooLarge)
    }
    /// Parse a character literal, starting after the opening quote.
    ///
    /// Before: chars{"\0' blah"}
    /// After:  chars{" blah"}
    fn parse_char(&mut self) -> Result<Token, String> {
        fn consume_until_quote(lexer: &mut Lexer) {
            loop {
                match lexer.parse_single_char(false) {
                    Ok(b'\'') => break,
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
            Ok(c) => match self.next_char() {
                Some(b'\'') => Ok(Literal::Char(c as u8).into()),
                Some(b'\n') => newline_err,
                None => term_err,
                Some(_) => {
                    consume_until_quote(self);
                    Err(String::from("Multi-character character literal"))
                }
            },
            Err(CharError::Eof) => term_err,
            Err(CharError::Newline) => newline_err,
            Err(CharError::Terminator) => Err(String::from("Empty character constant")),
            Err(CharError::HexTooLarge) => Err(String::from("hex character escape out of range")),
            Err(CharError::OctalTooLarge) => {
                Err(String::from("octal character escape out of range"))
            }
        }
    }
    /// Parse a string literal, starting before the opening quote.
    ///
    /// Concatenates multiple adjacent literals into one string.
    /// Adds a terminating null character, even if a null character has already been found.
    ///
    /// Before: u8s{"hello" "you" "it's me" mary}
    /// After:  chars{mary}
    fn parse_string(&mut self) -> Result<Token, String> {
        let mut literal = Vec::new();
        // allow multiple adjacent strings
        while self.peek() == Some(b'"') {
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
                    Err(CharError::HexTooLarge) => {
                        return Err(String::from("hex character escape out of range"))
                    }
                    Err(CharError::OctalTooLarge) => {
                        return Err(String::from("octal character escape out of range"))
                    }
                }
            }
            let old_saw_token = self.seen_line_token;
            self.consume_whitespace();
            // we're in a quandry here: we saw a newline, which reset `seen_line_token`,
            // but we're about to return a string, which will mistakenly reset it again.
            // HACK: `unput()` a newline, so that we'll reset `seen_line_token` again
            // HACK: on the following call to `next()`.
            // NOTE: since we saw a newline, we must have consumed at least one token,
            // NOTE: so this can't possibly discard `self.lookahead`.
            if self.seen_line_token != old_saw_token {
                self.unput(b'\n');
            }
        }
        literal.push(b'\0');
        Ok(Literal::Str(literal).into())
    }
    /// Parse an identifier or keyword, given the starting letter.
    ///
    /// Identifiers match the following regex: `[a-zA-Z_][a-zA-Z0-9_]*`
    fn parse_id(&mut self, start: u8) -> Result<Token, String> {
        let mut id = String::new();
        id.push(start.into());
        while let Some(c) = self.peek() {
            match c {
                b'0'..=b'9' | b'a'..=b'z' | b'A'..=b'Z' | b'_' => {
                    self.next_char();
                    id.push(c.into());
                }
                _ => break,
            }
        }
        Ok(Token::Id(InternedStr::get_or_intern(id)))
    }
}

impl Iterator for Lexer {
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
        // sanity check
        if self.chars.len() == 0 {
            return None;
        }

        self.consume_whitespace();
        let mut c = self.next_char().and_then(|c| {
            let span_start = self.location.offset - 1;
            // this giant switch is most of the logic
            let data = match c {
                b'#' => Token::Hash,
                b'+' => match self.peek() {
                    Some(b'=') => {
                        self.next_char();
                        AssignmentToken::AddEqual.into()
                    }
                    Some(b'+') => {
                        self.next_char();
                        Token::PlusPlus
                    }
                    _ => Token::Plus,
                },
                b'-' => match self.peek() {
                    Some(b'=') => {
                        self.next_char();
                        AssignmentToken::SubEqual.into()
                    }
                    Some(b'-') => {
                        self.next_char();
                        Token::MinusMinus
                    }
                    Some(b'>') => {
                        self.next_char();
                        Token::StructDeref
                    }
                    _ => Token::Minus,
                },
                b'*' => match self.peek() {
                    Some(b'=') => {
                        self.next_char();
                        AssignmentToken::MulEqual.into()
                    }
                    _ => Token::Star,
                },
                b'/' => {
                    if self.match_next(b'=') {
                        AssignmentToken::DivEqual.into()
                    } else {
                        Token::Divide
                    }
                }
                b'%' => match self.peek() {
                    Some(b'=') => {
                        self.next_char();
                        AssignmentToken::ModEqual.into()
                    }
                    _ => Token::Mod,
                },
                b'^' => {
                    if self.match_next(b'=') {
                        AssignmentToken::XorEqual.into()
                    } else {
                        Token::Xor
                    }
                }
                b'=' => match self.peek() {
                    Some(b'=') => {
                        self.next_char();
                        ComparisonToken::EqualEqual.into()
                    }
                    _ => Token::EQUAL,
                },
                b'!' => match self.peek() {
                    Some(b'=') => {
                        self.next_char();
                        ComparisonToken::NotEqual.into()
                    }
                    _ => Token::LogicalNot,
                },
                b'>' => match self.peek() {
                    Some(b'=') => {
                        self.next_char();
                        ComparisonToken::GreaterEqual.into()
                    }
                    Some(b'>') => {
                        self.next_char();
                        if self.match_next(b'=') {
                            AssignmentToken::ShrEqual.into()
                        } else {
                            Token::ShiftRight
                        }
                    }
                    _ => ComparisonToken::Greater.into(),
                },
                b'<' => match self.peek() {
                    Some(b'=') => {
                        self.next_char();
                        ComparisonToken::LessEqual.into()
                    }
                    Some(b'<') => {
                        self.next_char();
                        if self.match_next(b'=') {
                            AssignmentToken::ShlEqual.into()
                        } else {
                            Token::ShiftLeft
                        }
                    }
                    _ => ComparisonToken::Less.into(),
                },
                b'&' => match self.peek() {
                    Some(b'&') => {
                        self.next_char();
                        Token::LogicalAnd
                    }
                    Some(b'=') => {
                        self.next_char();
                        AssignmentToken::AndEqual.into()
                    }
                    _ => Token::Ampersand,
                },
                b'|' => match self.peek() {
                    Some(b'|') => {
                        self.next_char();
                        Token::LogicalOr
                    }
                    Some(b'=') => {
                        self.next_char();
                        AssignmentToken::OrEqual.into()
                    }
                    _ => Token::BitwiseOr,
                },
                b'{' => Token::LeftBrace,
                b'}' => Token::RightBrace,
                b'(' => Token::LeftParen,
                b')' => Token::RightParen,
                b'[' => Token::LeftBracket,
                b']' => Token::RightBracket,
                b'~' => Token::BinaryNot,
                b':' => Token::Colon,
                b';' => Token::Semicolon,
                b',' => Token::Comma,
                b'.' => match self.peek() {
                    Some(c) if c.is_ascii_digit() => match self.parse_float(10, String::new()) {
                        Ok(f) => Literal::Float(f).into(),
                        Err(err) => {
                            return Some(Err(Locatable {
                                data: err,
                                location: self.span(span_start),
                            }))
                        }
                    },
                    Some(b'.') => {
                        if self.peek_next() == Some(b'.') {
                            self.next_char();
                            self.next_char();
                            Token::Ellipsis
                        } else {
                            Token::Dot
                        }
                    }
                    _ => Token::Dot,
                },
                b'?' => Token::Question,
                b'0'..=b'9' => match self.parse_num(c) {
                    Ok(num) => num,
                    Err(err) => {
                        let span = self.span(span_start);
                        return Some(Err(span.with(err)));
                    }
                },
                b'a'..=b'z' | b'A'..=b'Z' | b'_' => match self.parse_id(c) {
                    Ok(id) => id,
                    Err(err) => {
                        let span = self.span(span_start);
                        return Some(Err(span.with(err)));
                    }
                },
                b'\'' => match self.parse_char() {
                    Ok(id) => id,
                    Err(err) => {
                        let span = self.span(span_start);
                        return Some(Err(span.with(err)));
                    }
                },
                b'"' => {
                    self.unput(b'"');
                    match self.parse_string() {
                        Ok(id) => id,
                        Err(err) => {
                            let span = self.span(span_start);
                            return Some(Err(span.with(err)));
                        }
                    }
                }
                x => {
                    return Some(Err(Locatable {
                        data: format!("unknown token {:?}", x),
                        location: self.span(span_start),
                    }))
                }
            };
            self.seen_line_token |= data != Token::Hash;
            Some(Ok(Locatable {
                data,
                location: self.span(span_start),
            }))
        });
        if c.is_none()
            && self.location.offset as usize == self.chars.len()
            && self.chars.as_bytes()[self.chars.len() - 1] != b'\n'
        {
            let err = Some(Err(CompileError::new(
                LexError::NoNewlineAtEOF.into(),
                self.span(self.chars.len() as u32 - 1),
            )));
            // HACK: avoid infinite loop
            self.location.offset += 1;
            return err;
        }
        // mark tokens as keywords if appropriate
        if let Some(Ok(Locatable {
            data: Token::Id(id),
            location,
        })) = &c
        {
            if let Some(keyword) = lookup_keyword(get_str!(id)) {
                c = Some(Ok(Locatable::new(Token::Keyword(keyword), *location)));
            }
        }
        if self.debug {
            if let Some(Ok(token)) = &c {
                println!("token: {}", token.data);
            }
        }
        // oof
        c.map(|result| result.map_err(|err| err.map(|err| LexError::Generic(err).into())))
            .or_else(|| self.error_handler.pop_front().map(Err))
    }
}

fn lookup_keyword(s: &str) -> Option<Keyword> {
    Some(match s {
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

        _ => return None,
    })
}
