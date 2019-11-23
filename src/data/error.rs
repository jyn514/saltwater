use thiserror::Error;

use super::{Locatable, Location};

#[derive(Debug, PartialEq, Eq, Error)]
pub enum CompileError {
    #[error("invalid token: {}", .0.data)]
    Lex(Locatable<String>),
    #[error("invalid syntax: {}", .0.data)]
    Syntax(Locatable<String>),
    #[error("invalid program: {}", .0.data)]
    Semantic(Locatable<String>),
}

pub type CompileResult<T> = Result<T, CompileError>;

impl From<Locatable<String>> for CompileError {
    fn from(err: Locatable<String>) -> Self {
        CompileError::Semantic(err)
    }
}

impl CompileError {
    pub fn location(&self) -> Location {
        match self {
            CompileError::Lex(err) => err.location,
            CompileError::Syntax(err) => err.location,
            CompileError::Semantic(err) => err.location,
        }
    }
    pub fn is_lex_err(&self) -> bool {
        match self {
            CompileError::Lex(_) => true,
            _ => false,
        }
    }
    pub fn is_syntax_err(&self) -> bool {
        match self {
            CompileError::Syntax(_) => true,
            _ => false,
        }
    }
    pub fn is_semantic_err(&self) -> bool {
        match self {
            CompileError::Semantic(_) => true,
            _ => false,
        }
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
