use std::fmt;

use thiserror::Error;

use super::{Expr, Locatable, Location};

pub type RecoverableResult<T = Expr, E = CompileError> = Result<T, (E, T)>;
pub type CompileResult<T> = Result<T, CompileError>;
pub type SemanticError = Locatable<String>;
pub type CompileError = Locatable<Error>;

#[derive(Debug, Error, PartialEq, Eq)]
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
}

impl Error {
    pub fn kind(&self) -> ErrorKind {
        use Error::*;
        match self {
            GenericLex(_) => ErrorKind::Lex,
            GenericSyntax(_) => ErrorKind::Syntax,
            GenericSemantic(_) => ErrorKind::Semantic,
            UnterminatedComment => ErrorKind::Lex,
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
    #[allow(non_snake_case)]
    pub(crate) fn Semantic(err: Locatable<String>) -> Self {
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

pub trait Recoverable {
    type Ok;
    type Error;
    fn into_inner<F: FnMut(Self::Error)>(self, error_handler: F) -> Self::Ok;
}

impl<T, E> Recoverable for Result<T, (E, T)> {
    type Ok = T;
    type Error = E;
    fn into_inner<F: FnMut(E)>(self, mut error_handler: F) -> T {
        match self {
            Ok(inner) => inner,
            Err((err, inner)) => {
                error_handler(err);
                inner
            }
        }
    }
}
