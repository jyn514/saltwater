use std::borrow::Cow;

use std::path::Path;
use crate::{Files, Source};
use super::{cpp::CppResult, Lexer};
use crate::{error::LexError, CompileError, data::{Locatable, CompileResult, Token}, Location};

pub(super) struct FileProcessor<'a> {
    /// The preprocessor collaborates extremely closely with the lexer,
    /// since it sometimes needs to know if a token is followed by whitespace.
    first_lexer: Lexer,
    /// Each lexer represents a separate source file that is currently being processed.
    includes: Vec<Lexer>,
    /// All known files, including files which have already been read.
    files: Files,
    /// The paths to search for `#include`d files
    search_path: Vec<Cow<'a, Path>>,
}

impl Iterator for FileProcessor<'_> {
    type Item = CompileResult<Locatable<Token>>;
    fn next(&mut self) -> Option<Self::Item> {
        loop {
            // we have to duplicate a bit of code here to avoid borrow errors
            let lexer = self.includes.last_mut().unwrap_or(&mut self.first_lexer);
            match lexer.next() {
                Some(token) => return Some(token),
                // finished this file, go on to the next one
                None => {
                    self.error_handler.append(&mut lexer.error_handler);
                    // this is the original source file
                    if self.includes.is_empty() {
                        return None;
                    } else {
                        self.includes.pop();
                    }
                }
            }
        }
    }
}

impl FileProcessor<'_> {
    /// Since there could potentially be multiple lexers (for multiple files),
    /// this is a convenience function that returns the lexer for the current file.
    pub fn lexer(&self) -> &Lexer {
        self.includes.last().unwrap_or(&self.first_lexer)
    }
    /// Same as `lexer()` but `&mut self -> &mut Lexer`.
    pub fn lexer_mut(&mut self) -> &mut Lexer {
        self.includes.last_mut().unwrap_or(&mut self.first_lexer)
    }
    pub fn add_file(&mut self, filename: String, source: Source) {
        let id = self.files.add(filename, source);
        self.includes.push(Lexer::new(id, source.code, self.first_lexer.debug));
    }

    /// Return a `Location` representing the end of the first file.
    pub fn eof(&self) -> Location {
        let lex = &self.first_lexer;
        Location {
            span: (lex.chars.len() as u32..lex.chars.len() as u32).into(),
            file: lex.location.file,
        }
    }

    /// Return all files loaded by the preprocessor, consuming it in the process.
    ///
    /// Files can be loaded by C source using `#include` directives.
    pub fn into_files(self) -> Files {
        self.files
    }

    /* Convenience functions */
    #[inline]
    fn line(&self) -> usize {
        self.lexer().line
    }
    #[inline]
    fn next_token(&mut self) -> Option<CppResult<Token>> {
        Some(self.lexer_mut().next()?.map_err(CompileError::from))
    }
    #[inline]
    fn span(&self, start: u32) -> Location {
        self.lexer().span(start)
    }
    #[inline]
    fn consume_whitespace(&mut self) {
        self.lexer_mut().consume_whitespace()
    }
    #[inline]
    fn seen_line_token(&self) -> bool {
        self.lexer().seen_line_token
    }
    #[inline]
    fn offset(&self) -> u32 {
        self.lexer().location.offset
    }

    /// Return all tokens from the current position until the end of the current line.
    ///
    /// Note that these are _tokens_ and not bytes, so if there are invalid tokens
    /// on the current line, this will return a lex error.
    fn tokens_until_newline(&mut self) -> Vec<CompileResult<Locatable<Token>>> {
        let mut tokens = Vec::new();
        let line = self.line();
        loop {
            self.consume_whitespace();
            if self.line() != line {
                // lines should end with a newline, but in case they don't, don't crash
                assert!(!self.lexer().seen_line_token || self.lexer_mut().peek().is_none(),
                    "expected `tokens_until_newline()` to reset `seen_line_token`, but `lexer.peek()` is {:?}",
                    self.lexer_mut().peek());
                break;
            }
            match self.next() {
                Some(token) => tokens.push(token),
                None => break,
            }
        }
        tokens
    }
}