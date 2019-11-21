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
}
