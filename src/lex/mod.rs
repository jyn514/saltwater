use std::convert::{TryFrom, TryInto};
use std::rc::Rc;

use codespan::FileId;

use super::data::{error::LexError, lex::*, *};
use super::intern::InternedStr;

mod cpp;
mod files;
pub mod replace;
#[cfg(test)]
mod tests;
// https://github.com/rust-lang/rust/issues/64762
#[allow(unreachable_pub)]
pub use cpp::{PreProcessor, PreProcessorBuilder};
#[allow(unreachable_pub)]
pub use replace::Definition;

type LexResult<T = Token> = Result<T, Locatable<LexError>>;

/// A Lexer takes the source code and turns it into tokens with location information.
///
/// Tokens are either literals, keywords, identifiers, or builtin operations.
/// This allows the parser to worry about fewer things at a time.
/// Location information is irritating to deal with but allows for better error messages.
/// This is the reason the filename is mandatory, so that it can be shown in errors.
/// You may also find the `warn` and `error` functions in `utils.rs` to be useful.
///
/// Lexer implements iterator, so you can loop over the tokens.
#[derive(Debug)]
pub struct Lexer {
    location: SingleLocation,
    chars: Rc<str>,
    /// used for 2-character tokens
    current: Option<char>,
    /// used for 3-character tokens
    lookahead: Option<char>,
    /// whether we've a token on this line before or not
    /// used for preprocessing (e.g. `#line 5` is a directive
    /// but `int main() { # line 5` is not)
    seen_line_token: bool,
    /// counts _logical_ lines, not physical lines
    /// used for the preprocessor (mostly for `tokens_until_newline()`)
    line: usize,
    error_handler: ErrorHandler<LexError>,
    /// Whether or not to display each token as it is processed
    debug: bool,
    given_newline_error: bool,
}

// returned when lexing a string literal
enum CharError {
    Eof,
    Newline,
    Terminator,
    OctalTooLarge,
    HexTooLarge,
    MultiByte,
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
            given_newline_error: false,
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
    fn next_char(&mut self) -> Option<char> {
        let mut c = self._next_char();
        // Section 5.1.1.2 phase 2: discard backslashes before newlines
        while c == Some('\\') && self.peek() == Some('\n') {
            self._next_char(); // discard \n
            self.consume_whitespace();
            c = self._next_char();
        }
        if c == Some('\n') {
            self.seen_line_token = false;
            self.line += 1;
        }
        c
    }
    // Internal use only, use `next_char()` instead.
    // This gets the next token from the buffer
    // and updates the current offset and relevant fields.
    fn _next_char(&mut self) -> Option<char> {
        if let c @ Some(_) = self.current {
            self.current = self.lookahead.take();
            c
        } else {
            assert!(self.lookahead.is_none());
            self.chars().next()
        }
        .map(|c| {
            self.location.offset += c.len_utf8() as u32;
            c
        })
    }

    // TODO: this _really_ needs to be refactored
    fn chars(&self) -> std::str::Chars<'_> {
        use std::mem;

        // if we're compiling on 16-bit, we have bigger problems
        const_assert!(mem::size_of::<usize>() >= mem::size_of::<u32>());
        self.chars[self.location.offset as usize..].chars()
    }

    /// Return the character that would be returned by `next_char`.
    /// Can be called any number of the times and will still return the same result.
    fn peek(&mut self) -> Option<char> {
        self.current = self
            .current
            .or_else(|| self.lookahead.take())
            .or_else(|| self.chars().next());
        self.current
    }
    /// Return the character that would be returned if you called `next_char()` twice in a row.
    /// Can be called any number of the times and will still return the same result.
    fn peek_next(&mut self) -> Option<char> {
        self.lookahead = self.lookahead.or_else(|| self.chars().nth(1));
        self.lookahead
    }
    /// Return a single token to the stream.
    /// Can be called at most once before running out of space to store the token.
    ///
    /// # Panics
    /// This function will panic if called twice in a row
    /// or when `self.lookahead.is_some()`.
    fn unput(&mut self, byte: char) {
        assert!(
            self.lookahead.is_none(),
            "unputting {:?} would cause the lexer to forget it saw {:?} (current is {:?})",
            byte as char,
            self.lookahead.unwrap() as char,
            self.current.unwrap() as char
        );
        self.lookahead = self.current.take();
        self.current = Some(byte);
        // TODO: this is not right,
        // it will break if someone calls `span()` before consuming the newline
        self.location.offset -= 1;
    }
    /// If the next character is `item`, consume it and return true.
    /// Otherwise, return false.
    fn match_next(&mut self, item: char) -> bool {
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

    #[inline]
    fn consume_whitespace(&mut self) -> String {
        self.consume_whitespace_full(false, true)
    }
    #[inline]
    fn consume_whitespace_preprocessor(&mut self) -> String {
        self.consume_whitespace_full(true, false)
    }
    /// Remove all consecutive whitespace pending in the stream.
    /// This includes comments.
    ///
    /// If `stop_at_newline` this stops at the end of the line (unless there's a comment)
    /// If `comments_newlines` then multiline comments are replaced with their newlines else space
    ///
    /// Before: b"    // some comment\n /*multi comment*/hello   "
    /// After:  b"hello   "
    fn consume_whitespace_full(
        &mut self,
        stop_at_newline: bool,
        comments_newlines: bool,
    ) -> String {
        // there may be comments following whitespace
        let mut whitespace = String::new();
        loop {
            // whitespace
            while self.peek().map_or(false, |c| {
                c.is_ascii_whitespace() && !(stop_at_newline && c == '\n')
            }) {
                if let Some(c) = self.next_char() {
                    whitespace.push(c);
                }
            }
            // comments
            if self.peek() == Some('/') {
                match self.peek_next() {
                    Some('/') => self.consume_line_comment(),
                    Some('*') => {
                        self.next_char();
                        self.next_char();
                        match self.consume_multi_comment() {
                            Ok(ws) => {
                                let ws = if comments_newlines { &ws } else { " " };
                                whitespace.push_str(ws)
                            }
                            Err(err) => self.error_handler.push_back(err),
                        }
                    }
                    _ => break,
                }
            } else {
                break;
            }
        }
        whitespace
    }
    /// Remove all characters between now and the next '\n' character.
    ///
    /// Before: u8s{"blah `invalid tokens``\nhello // blah"}
    /// After:  chars{"hello // blah"}
    fn consume_line_comment(&mut self) {
        loop {
            match self.peek() {
                None | Some('\n') => return,
                _ => {
                    self.next_char();
                }
            }
        }
    }
    /// Remove a multi-line C-style comment, i.e. until the next '*/'.
    ///
    /// Before: u8s{"hello this is a lot of text */ int main(){}"}
    /// After:  chars{" int main(){}"}
    ///
    /// Return newlines occupied by the comment or a space if no newlines
    fn consume_multi_comment(&mut self) -> LexResult<String> {
        let mut whitespace = String::new();
        let start = self.location.offset - 2;
        while let Some(c) = self.next_char() {
            if c == '*' && self.peek() == Some('/') {
                self.next_char();
                if whitespace.is_empty() {
                    whitespace.push(' '); // For the case `a/* */b`
                }
                return Ok(whitespace);
            }
            if c == '\n' {
                whitespace.push(c);
            }
        }
        Err(Locatable {
            location: self.span(start),
            data: LexError::UnterminatedComment,
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
    fn parse_num(&mut self, start: char) -> Result<Token, LexError> {
        // start - '0' breaks for hex digits
        assert!(
            '0' <= start && start <= '9',
            "main loop should only pass [-.0-9] as start to parse_num"
        );
        let span_start = self.location.offset - 1; // -1 for `start`
        let float_literal = |f| Token::Literal(Literal::Float(f));
        let mut buf = String::new();
        buf.push(start as char);
        // check for radix other than 10 - but if we see '.', use 10
        let radix = if start == '0' {
            if self.match_next('b') {
                Radix::Binary
            } else if self.match_next('x') {
                buf.push('x');
                Radix::Hexadecimal
            } else if self.match_next('.') {
                // float: 0.431
                return self.parse_float(Radix::Decimal, buf).map(float_literal);
            } else {
                // octal: 0755 => 493
                Radix::Octal
            }
        } else {
            Radix::Decimal
        };
        let start = start as u64 - '0' as u64;

        // the first {digits} in the regex
        let digits = match self.parse_int(start, radix, &mut buf)? {
            Some(int) => int,
            None => {
                if radix == Radix::Octal || radix == Radix::Decimal || self.peek() == Some('.') {
                    start
                } else {
                    return Err(LexError::MissingDigits(radix.try_into().unwrap()));
                }
            }
        };
        if self.match_next('.') {
            return self.parse_float(radix, buf).map(float_literal);
        }
        if let Some('e') | Some('E') | Some('p') | Some('P') = self.peek() {
            buf.push_str(".0"); // hexf doesn't like floats without a decimal point
            let float = self.parse_exponent(radix == Radix::Hexadecimal, buf);
            self.consume_float_suffix();
            return float.map(float_literal);
        }
        let literal = if self.match_next('u') || self.match_next('U') {
            let unsigned = u64::try_from(digits).map_err(|_| LexError::IntegerOverflow {
                is_signed: Some(false),
            })?;
            Literal::UnsignedInt(unsigned)
        } else {
            let long = i64::try_from(digits).map_err(|_| LexError::IntegerOverflow {
                is_signed: Some(true),
            })?;
            Literal::Int(long)
        };
        // get rid of 'l' and 'll' suffixes, we don't handle them
        if self.match_next('l') {
            self.match_next('l');
        } else if self.match_next('L') {
            self.match_next('L');
        }
        if radix == Radix::Binary {
            let span = self.span(span_start);
            self.error_handler
                .warn("binary number literals are an extension", span);
        }
        Ok(Token::Literal(literal))
    }
    // at this point we've already seen a '.', if we see one again it's an error
    fn parse_float(&mut self, radix: Radix, mut buf: String) -> Result<f64, LexError> {
        buf.push('.');
        // parse fraction: second {digits} in regex
        while let Some(c) = self.peek() {
            let c = c as char;
            if c.is_digit(radix.as_u8().into()) {
                self.next_char();
                buf.push(c);
            } else {
                break;
            }
        }
        // in case of an empty mantissa, hexf doesn't like having the exponent right after the .
        // if the mantissa isn't empty, .12 is the same as .120
        //buf.push('0');
        let float = self.parse_exponent(radix == Radix::Hexadecimal, buf);
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
    fn parse_exponent(&mut self, hex: bool, mut buf: String) -> Result<f64, LexError> {
        let is_digit =
            |c: Option<char>| c.map_or(false, |c| (c as char).is_digit(10) || c == '+' || c == '-');
        if hex {
            if self.match_next('p') || self.match_next('P') {
                if !is_digit(self.peek()) {
                    return Err(LexError::ExponentMissingDigits);
                }
                buf.push('p');
                buf.push(self.next_char().unwrap() as char);
            }
        } else if self.match_next('e') || self.match_next('E') {
            if !is_digit(self.peek()) {
                return Err(LexError::ExponentMissingDigits);
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
        let float: f64 = if hex {
            let float_literal: hexponent::FloatLiteral = buf.parse()?;
            float_literal.into()
        } else {
            buf.parse()?
        };
        let should_be_zero = buf.chars().all(|c| match c {
            '.' | '+' | '-' | 'e' | 'p' | '0' => true,
            _ => false,
        });
        if float == 0.0 && !should_be_zero {
            Err(LexError::FloatUnderflow)
        } else {
            Ok(float)
        }
    }
    // returns None if there are no digits at the current position
    fn parse_int(
        &mut self,
        mut acc: u64,
        radix: Radix,
        buf: &mut String,
    ) -> Result<Option<u64>, LexError> {
        let parse_digit = |c: char| match c.to_digit(16) {
            None => Ok(None),
            Some(digit) if digit < radix.as_u8().into() => Ok(Some(digit)),
            // if we see 'e' or 'E', it's the end of the int, don't treat it as an error
            // if we see 'b' this could be part of a binary constant (0b1)
            // if we see 'f' it could be a float suffix
            // we only get this far if it's not a valid digit for the radix, i.e. radix != 16
            Some(11) | Some(14) | Some(15) => Ok(None),
            Some(digit) => Err(LexError::InvalidDigit { digit, radix }),
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
                .checked_mul(radix.as_u8().into())
                .and_then(|a| a.checked_add(digit.into()));
            match maybe_digits {
                Some(digits) => acc = digits,
                None => err = true,
            }
        }
        if err {
            Err(LexError::IntegerOverflow { is_signed: None })
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
        let terminator = if string { '"' } else { '\'' };
        if let Some(c) = self.next_char() {
            if c == '\\' {
                if let Some(c) = self.next_char() {
                    Ok(match c {
                        // escaped newline: "a\
                        // b"
                        '\n' => unreachable!("should be handled earlier"),
                        'n' => b'\n',   // embedded newline: "a\nb"
                        'r' => b'\r',   // carriage return
                        't' => b'\t',   // tab
                        '"' => b'"',    // escaped "
                        '\'' => b'\'',  // escaped '
                        '\\' => b'\\',  // \
                        'a' => b'\x07', // bell
                        'b' => b'\x08', // backspace
                        'v' => b'\x0b', // vertical tab
                        'f' => b'\x0c', // form feed
                        '?' => b'?',    // a literal '?', for trigraphs
                        '0'..='9' => {
                            return self.parse_octal_char_escape(c).map_err(|err| {
                                // try to avoid extraneous errors, but don't try too hard
                                self.match_next('\'');
                                err
                            });
                        }
                        'x' => {
                            return self.parse_hex_char_escape().map_err(|err| {
                                // try to avoid extraneous errors, but don't try too hard
                                self.match_next('\'');
                                err
                            });
                        }
                        '\0'..='\x7f' => {
                            self.error_handler.warn(
                                &format!("unknown character escape '\\{}'", c),
                                self.span(self.location.offset - 1),
                            );
                            c as u8
                        }
                        _ => return Err(CharError::MultiByte),
                    })
                } else {
                    Err(CharError::Eof)
                }
            } else if c == '\n' {
                Err(CharError::Newline)
            } else if c == terminator {
                Err(CharError::Terminator)
            } else if c.is_ascii() {
                Ok(c as u8)
            } else {
                Err(CharError::MultiByte)
            }
        } else {
            Err(CharError::Eof)
        }
    }
    fn parse_octal_char_escape(&mut self, start: char) -> Result<u8, CharError> {
        // char::to_digit without the `unwrap()`
        let to_digit = |c| c as u32 - '0' as u32;
        let mut base = to_digit(start);
        // at most 3 digits in an octal constant, `start` is the first so only 2 possible left
        for _ in 0..2 {
            match self.peek() {
                Some(c) if '0' <= c && c < '8' => {
                    self.next_char();
                    base <<= 3; // base *= 8
                    base += to_digit(c);
                }
                _ => break,
            }
        }
        base.try_into().map_err(|_| CharError::OctalTooLarge)
    }
    fn parse_hex_char_escape(&mut self) -> Result<u8, CharError> {
        // first, consume the hex literal so overflow errors don't cascade
        let mut buf = Vec::new();
        while let Some(c) = self.peek() {
            match c.to_digit(16) {
                Some(c) => {
                    self.next_char();
                    buf.push(c);
                }
                None => break,
            }
        }

        // now, turn the literal into a number
        let mut base = 0_u64;
        for digit in buf {
            base = base.checked_mul(16).ok_or(CharError::HexTooLarge)?;
            // NOTE: because we shifted in a 0 and c < 16, this can't overflow
            base += u64::from(digit);
        }
        // the largest three digit octal is \777, but C characters are bytes and can only store up to 255
        u8::try_from(base).or(Err(CharError::HexTooLarge))
    }
    /// Parse a character literal, starting after the opening quote.
    ///
    /// Before: chars{"\0' blah"}
    /// After:  chars{" blah"}
    fn parse_char(&mut self) -> Result<Token, LexError> {
        fn consume_until_quote(lexer: &mut Lexer) {
            loop {
                match lexer.parse_single_char(false) {
                    Ok(b'\'') => break,
                    Err(_) => break,
                    _ => {}
                }
            }
        }
        match self.parse_single_char(false) {
            Ok(c) => match self.next_char() {
                Some('\'') => Ok(Literal::Char(c).into()),
                Some('\n') => Err(LexError::NewlineInChar),
                None => Err(LexError::MissingEndQuote { string: false }),
                Some(_) => {
                    consume_until_quote(self);
                    Err(LexError::MultiByteCharLiteral)
                }
            },
            Err(CharError::Eof) => Err(LexError::MissingEndQuote { string: false }),
            Err(CharError::Newline) => Err(LexError::NewlineInChar),
            Err(CharError::Terminator) => Err(LexError::EmptyChar),
            Err(CharError::HexTooLarge) => Err(LexError::CharEscapeOutOfRange(Radix::Hexadecimal)),
            Err(CharError::OctalTooLarge) => Err(LexError::CharEscapeOutOfRange(Radix::Octal)),
            Err(CharError::MultiByte) => Err(LexError::MultiByteCharLiteral),
        }
    }
    /// Parse a string literal, starting before the opening quote.
    ///
    /// Concatenates multiple adjacent literals into one string.
    /// Adds a terminating null character, even if a null character has already been found.
    ///
    /// Before: u8s{"hello" "you" "it's me" mary}
    /// After:  chars{mary}
    fn parse_string(&mut self) -> Result<Token, LexError> {
        let mut literal = Vec::new();
        // allow multiple adjacent strings
        while self.peek() == Some('"') {
            self.next_char(); // start quote
            loop {
                match self.parse_single_char(true) {
                    Ok(c) => literal.push(c),
                    Err(CharError::Eof) => {
                        return Err(LexError::MissingEndQuote { string: true });
                    }
                    Err(CharError::Newline) => {
                        return Err(LexError::NewlineInString);
                    }
                    Err(CharError::Terminator) => break,
                    Err(CharError::MultiByte) => return Err(LexError::MultiByteCharLiteral),
                    Err(CharError::HexTooLarge) => {
                        return Err(LexError::CharEscapeOutOfRange(Radix::Hexadecimal));
                    }
                    Err(CharError::OctalTooLarge) => {
                        return Err(LexError::CharEscapeOutOfRange(Radix::Octal));
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
            if self.seen_line_token != old_saw_token && self.peek() != Some('"') {
                self.unput('\n');
            }
        }
        literal.push(b'\0');
        Ok(Literal::Str(literal).into())
    }
    /// Parse an identifier or keyword, given the starting letter.
    ///
    /// Identifiers match the following regex: `[a-zA-Z_][a-zA-Z0-9_]*`
    fn parse_id(&mut self, start: char) -> Result<Token, LexError> {
        let mut id = String::new();
        id.push(start);
        while let Some(c) = self.peek() {
            match c {
                '0'..='9' | 'a'..='z' | 'A'..='Z' | '_' => {
                    self.next_char();
                    id.push(c);
                }
                _ => break,
            }
        }
        Ok(Token::Id(InternedStr::get_or_intern(id)))
    }

    /// Returns next token in stream which is not whitespace
    pub fn next_non_whitespace(&mut self) -> Option<LexResult<Locatable<Token>>> {
        loop {
            match self.next() {
                Some(Ok(Locatable {
                    data: Token::Whitespace(_),
                    ..
                })) => continue,
                other => break other,
            }
        }
    }
}

impl Iterator for Lexer {
    // option: whether the stream is exhausted
    // result: whether the next lexeme is an error
    type Item = LexResult<Locatable<Token>>;

    /// Return the next token in the stream.
    ///
    /// This iterator never resumes after it is depleted,
    /// i.e. once it returns None once, it will always return None.
    ///
    /// Any item may be an error, but items will always have an associated location.
    /// The file may be empty to start, in which case the iterator will return None.
    fn next(&mut self) -> Option<Self::Item> {
        if let Some(err) = self.error_handler.pop_front() {
            return Some(Err(err));
        }

        // sanity check
        if self.chars.len() == self.location.offset as usize {
            return None;
        }

        let check_no_newline = |this: &mut Self| {
            // TODO: this is awful
            if this.location.offset as usize == this.chars.len() && !this.chars.ends_with('\n') {
                let location = this.span(this.chars.len() as u32);
                this.error_handler
                    .push_back(location.with(LexError::NoNewlineAtEOF));
            }
        };

        {
            let span_start = self.location.offset;
            let data = self.consume_whitespace();
            check_no_newline(self);
            if !data.is_empty() {
                return Some(Ok(Locatable {
                    data: Token::Whitespace(data),
                    location: self.span(span_start),
                }));
            }
        };

        let c = self.next_char().and_then(|c| {
            let span_start = self.location.offset - c.len_utf8() as u32;
            // this giant switch is most of the logic
            let data = match c {
                '#' => Token::Hash,
                '+' => match self.peek() {
                    Some('=') => {
                        self.next_char();
                        AssignmentToken::AddEqual.into()
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
                        AssignmentToken::SubEqual.into()
                    }
                    Some('-') => {
                        self.next_char();
                        Token::MinusMinus
                    }
                    Some('>') => {
                        self.next_char();
                        Token::StructDeref
                    }
                    _ => Token::Minus,
                },
                '*' => match self.peek() {
                    Some('=') => {
                        self.next_char();
                        AssignmentToken::MulEqual.into()
                    }
                    _ => Token::Star,
                },
                '/' => {
                    if self.match_next('=') {
                        AssignmentToken::DivEqual.into()
                    } else {
                        Token::Divide
                    }
                }
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
                            AssignmentToken::ShrEqual.into()
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
                            AssignmentToken::ShlEqual.into()
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
                    Some(c) if c.is_ascii_digit() => {
                        match self.parse_float(Radix::Decimal, String::new()) {
                            Ok(f) => Literal::Float(f).into(),
                            Err(err) => {
                                return Some(Err(Locatable {
                                    data: err,
                                    location: self.span(span_start),
                                }))
                            }
                        }
                    }
                    Some('.') => {
                        if self.peek_next() == Some('.') {
                            self.next_char();
                            self.next_char();
                            Token::Ellipsis
                        } else {
                            Token::Dot
                        }
                    }
                    _ => Token::Dot,
                },
                '?' => Token::Question,
                '0'..='9' => match self.parse_num(c) {
                    Ok(num) => num,
                    Err(err) => {
                        let span = self.span(span_start);
                        return Some(Err(span.with(err)));
                    }
                },
                'a'..='z' | 'A'..='Z' | '_' => match self.parse_id(c) {
                    Ok(id) => id,
                    Err(err) => {
                        let span = self.span(span_start);
                        return Some(Err(span.with(err)));
                    }
                },
                '\'' => match self.parse_char() {
                    Ok(id) => id,
                    Err(err) => {
                        let span = self.span(span_start);
                        return Some(Err(span.with(err)));
                    }
                },
                '"' => {
                    self.unput('"');
                    match self.parse_string() {
                        Ok(id) => id,
                        Err(err) => {
                            let span = self.span(span_start);
                            return Some(Err(span.with(err)));
                        }
                    }
                }
                x => {
                    return Some(Err(self
                        .span(span_start)
                        .with(LexError::UnknownToken(x as char))));
                }
            };
            // We've seen a token if this isn't # or whitespace
            self.seen_line_token |= !(data == Token::Hash || matches!(data, Token::Whitespace(_)));
            Some(Ok(Locatable {
                data,
                location: self.span(span_start),
            }))
        });

        if self.debug {
            if let Some(Ok(token)) = &c {
                println!("token: {}", token.data);
            }
        }
        c.or_else(|| self.error_handler.pop_front().map(Err))
    }
}
