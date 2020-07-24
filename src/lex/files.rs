use super::Lexer;
use crate::{
    data::{CompileResult, Locatable, Token},
    ErrorHandler, Location,
};
use crate::{Files, Source};
use std::collections::VecDeque;
use std::path::{Path, PathBuf};
use std::rc::Rc;

enum TokenSource {
    Lexer(Lexer),
    Precompiled(VecDeque<Locatable<Token>>),
}

impl From<VecDeque<Locatable<Token>>> for TokenSource {
    fn from(queue: VecDeque<Locatable<Token>>) -> Self {
        Self::Precompiled(queue)
    }
}

impl From<Lexer> for TokenSource {
    fn from(lexer: Lexer) -> Self {
        Self::Lexer(lexer)
    }
}

impl Iterator for TokenSource {
    type Item = super::LexResult<Locatable<Token>>;
    fn next(&mut self) -> Option<Self::Item> {
        match self {
            Self::Lexer(l) => l.next(),
            Self::Precompiled(queue) => queue.pop_front().map(Ok),
        }
    }
}

// TODO: this API is absolutely terrible, there's _no_ encapsulation
pub(super) struct FileProcessor {
    /// The preprocessor collaborates extremely closely with the lexer,
    /// since it sometimes needs to know if a token is followed by whitespace.
    first_lexer: Lexer,
    /// Each lexer represents a separate source file that is currently being processed.
    includes: Vec<TokenSource>,
    /// All known files, including files which have already been read.
    files: Files,
    pub(super) error_handler: ErrorHandler,
    current: Option<CompileResult<Locatable<Token>>>,
}

impl Iterator for FileProcessor {
    type Item = CompileResult<Locatable<Token>>;
    fn next(&mut self) -> Option<Self::Item> {
        let first_lexer = &mut self.first_lexer;
        loop {
            // we have to duplicate a bit of code here to avoid borrow errors
            let mut lexer = self.includes.last_mut();
            match self.current.take().or_else(|| {
                match &mut lexer {
                    None => first_lexer.next(),
                    Some(l) => l.next(),
                }
                .map(|res| res.map_err(Into::into))
            }) {
                Some(token) => return Some(token),
                // finished this file, go on to the next one
                None => {
                    if let Some(TokenSource::Lexer(lexer)) = lexer {
                        self.error_handler.append(&mut lexer.error_handler);
                    }
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

impl FileProcessor {
    pub(super) fn new(
        chars: impl Into<Rc<str>>,
        filename: impl Into<std::ffi::OsString>,
        debug: bool,
    ) -> Self {
        let mut files = Files::new();
        let chars = chars.into();
        let filename = filename.into();
        let source = crate::Source {
            code: Rc::clone(&chars),
            path: filename.clone().into(),
        };
        let file = files.add(filename, source);
        Self {
            error_handler: ErrorHandler::default(),
            first_lexer: Lexer::new(file, chars, debug),
            files,
            includes: Default::default(),
            current: None,
        }
    }

    pub(super) fn peek(&mut self) -> Option<&CompileResult<Locatable<Token>>> {
        if self.current.is_none() {
            self.current = self.next();
        }
        self.current.as_ref()
    }

    /// Since there could potentially be multiple lexers (for multiple files),
    /// this is a convenience function that returns the lexer for the current file.
    pub(super) fn lexer(&self) -> &Lexer {
        self.includes
            .iter()
            .rev()
            .filter_map(|source| match source {
                TokenSource::Lexer(l) => Some(l),
                TokenSource::Precompiled(_) => None,
            })
            .next()
            .unwrap_or(&self.first_lexer)
    }
    /// Same as `lexer()` but `&mut self -> &mut Lexer`.
    pub(super) fn lexer_mut(&mut self) -> &mut Lexer {
        self.includes
            .iter_mut()
            .rev()
            .filter_map(|source| match source {
                TokenSource::Lexer(l) => Some(l),
                TokenSource::Precompiled(_) => None,
            })
            .next()
            .unwrap_or(&mut self.first_lexer)
    }
    pub(super) fn add_file(&mut self, filename: PathBuf, source: Source) {
        let code = Rc::clone(&source.code);
        let id = self.files.add(filename, source);
        self.includes
            .push(Lexer::new(id, code, self.first_lexer.debug).into());
    }

    pub(super) fn add_precompiled_file(&mut self, tokens: VecDeque<Locatable<Token>>) {
        self.includes.push(TokenSource::Precompiled(tokens));
    }

    /// Return a `Location` representing the end of the first file.
    pub(super) fn eof(&self) -> Location {
        let lex = &self.first_lexer;
        Location {
            span: (lex.chars.len() as u32..lex.chars.len() as u32).into(),
            file: lex.location.file,
        }
    }

    /// Return all files loaded by the preprocessor, consuming it in the process.
    ///
    /// Files can be loaded by C source using `#include` directives.
    pub(super) fn into_files(self) -> Files {
        self.files
    }

    /* Convenience functions */
    #[inline]
    pub(super) fn line(&self) -> usize {
        self.lexer().line
    }
    #[inline]
    pub(super) fn span(&self, start: u32) -> Location {
        self.lexer().span(start)
    }
    #[inline]
    pub(super) fn consume_whitespace(&mut self) -> String {
        self.lexer_mut().consume_whitespace()
    }
    #[inline]
    pub(super) fn consume_whitespace_preprocessor(&mut self) -> String {
        self.lexer_mut().consume_whitespace_preprocessor()
    }
    #[inline]
    pub(super) fn seen_line_token(&self) -> bool {
        self.lexer().seen_line_token
    }
    #[inline]
    pub(super) fn offset(&self) -> u32 {
        self.lexer().location.offset
    }

    /* These functions are really for the benefit of `PreProcessor`, not anyone else. */
    pub(super) fn path(&self) -> &Path {
        &self.files.source(self.lexer().location.file).path
    }

    /// Return all tokens from the current position until the end of the current line.
    ///
    /// * `whitespace` - whether or not to include whitespace tokens
    ///
    /// Note that these are _tokens_ and not bytes, so if there are invalid tokens
    /// on the current line, this will return a lex error.
    pub(super) fn tokens_until_newline(
        &mut self,
        whitespace: bool,
    ) -> Vec<CompileResult<Locatable<Token>>> {
        let mut tokens = Vec::new();
        loop {
            let ws_start = self.offset();
            let ws = self.consume_whitespace_preprocessor();
            let ws_span = self.span(ws_start);
            if whitespace && !ws.is_empty() {
                tokens.push(Ok(Locatable {
                    data: Token::Whitespace(ws), // NOTE: in clang, this is one space
                    location: ws_span,
                }));
            }
            if self.lexer_mut().peek().unwrap_or('\n') == '\n' {
                break;
            }
            match self.next() {
                Some(token) => tokens.push(token),
                None => break,
            }
        }
        tokens
    }

    /// Returns next token in stream which is not whitespace
    pub(super) fn next_non_whitespace(&mut self) -> Option<CompileResult<Locatable<Token>>> {
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
