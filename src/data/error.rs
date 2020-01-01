use std::fmt;

use thiserror::Error;

use super::{Locatable, Location};

pub type RecoverableResult<T, E = CompileError> = Result<T, (E, T)>;
pub type CompileResult<T> = Result<T, CompileError>;
pub type SemanticError = Locatable<String>;
pub type CompileError = Locatable<Error>;

#[derive(Debug, Default)]
pub struct ErrorHandler {
    errors: Vec<CompileError>,
}

impl ErrorHandler {
    pub fn new() -> ErrorHandler {
        Default::default()
    }

    pub fn push_err(&mut self, error: CompileError) {
        self.errors.push(error);
    }

    #[must_use]
    pub fn is_successful(&self) -> bool {
        self.errors.is_empty()
    }
}

impl<'a> IntoIterator for &'a ErrorHandler {
    type Item = &'a CompileError;
    type IntoIter = <&'a Vec<CompileError> as IntoIterator>::IntoIter;

    fn into_iter(self) -> Self::IntoIter {
        self.errors.iter()
    }
}

impl IntoIterator for ErrorHandler {
    type Item = CompileError;
    type IntoIter = <Vec<CompileError> as IntoIterator>::IntoIter;

    fn into_iter(self) -> Self::IntoIter {
        self.errors.into_iter()
    }
}

#[derive(Debug, Error, PartialEq, Eq)]
/// errors are non-exhaustive and may have new variants added at any time
pub enum Error {
    // for compatibility with previous error system
    #[error("{0}")]
    GenericLex(String),
    #[error("{0}")]
    GenericSyntax(String),
    #[error("{0}")]
    GenericSemantic(String),

    // specific errors
    #[error("unterminated /* comment")]
    UnterminatedComment,

    #[doc(hidden)]
    #[error("internal error: do not construct nonexhaustive variants")]
    __Nonexhaustive,
}

impl Error {
    pub fn kind(&self) -> ErrorKind {
        use Error::*;
        match self {
            GenericLex(_) => ErrorKind::Lex,
            GenericSyntax(_) => ErrorKind::Syntax,
            GenericSemantic(_) => ErrorKind::Semantic,
            UnterminatedComment => ErrorKind::Lex,
            __Nonexhaustive => panic!("do not construct nonexhaustive variants manually"),
        }
    }
}

#[derive(Debug, PartialEq, Eq, Error)]
pub enum ErrorKind {
    #[error("invalid token")]
    Lex,
    #[error("invalid syntax")]
    Syntax,
    #[error("invalid program")]
    Semantic,
}

impl CompileError {
    pub(crate) fn semantic(err: Locatable<String>) -> Self {
        Self::from(err)
    }
    pub fn location(&self) -> Location {
        self.location
    }
    pub fn is_lex_err(&self) -> bool {
        self.data.kind() == ErrorKind::Lex
    }
    pub fn is_syntax_err(&self) -> bool {
        self.data.kind() == ErrorKind::Syntax
    }
    pub fn is_semantic_err(&self) -> bool {
        self.data.kind() == ErrorKind::Semantic
    }
}

impl fmt::Display for CompileError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}: {}", self.data.kind(), self.data)
    }
}

#[derive(Debug, PartialEq, Eq, Error)]
#[error("{}", .0.data)]
pub struct SyntaxError(pub Locatable<String>);

impl From<Locatable<String>> for CompileError {
    fn from(err: Locatable<String>) -> Self {
        err.map(Error::GenericSemantic)
    }
}

impl From<SyntaxError> for CompileError {
    fn from(err: SyntaxError) -> Self {
        err.0.map(Error::GenericSyntax)
    }
}

impl From<Locatable<String>> for SyntaxError {
    fn from(err: Locatable<String>) -> Self {
        Self(err)
    }
}

pub trait Recover {
    type Ok;
    fn recover(self, error_handler: &mut ErrorHandler) -> Self::Ok;
}

impl<T, E: Into<CompileError>> Recover for RecoverableResult<T, E> {
    type Ok = T;
    fn recover(self, error_hander: &mut ErrorHandler) -> T {
        self.unwrap_or_else(|(e, i)| {
            error_hander.push_err(e.into());
            i
        })
    }
}

impl<T, E: Into<CompileError>> Recover for RecoverableResult<T, Vec<E>> {
    type Ok = T;
    fn recover(self, error_handler: &mut ErrorHandler) -> T {
        self.unwrap_or_else(|(es, i)| {
            for e in es {
                error_handler.push_err(e.into());
            }
            i
        })
    }
}
