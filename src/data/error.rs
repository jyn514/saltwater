use thiserror::Error;

use super::{Expr, Locatable, Location};

pub type RecoverableResult<T = Expr, E = CompileError> = Result<T, (E, T)>;
pub type CompileResult<T> = Result<T, CompileError>;
pub type SemanticError = Locatable<String>;

#[derive(Debug, PartialEq, Eq, Error)]
pub enum ErrorKind {
    #[error("invalid token")]
    Lex,
    #[error("invalid syntax")]
    Syntax,
    #[error("invalid program")]
    Semantic,
}

// TODO: remove this and use Locatable<Error>
pub struct CompileError {
    error: Error,
    location: Location,
}

#[derive(Debug)]
pub enum Error {
    GenericLex(Locatable<String>),
    GenericSyntax(SyntaxError),
    GenericSemantic(Locatable<String>),
}

#[derive(Debug, PartialEq, Eq, Error)]
#[error("{}", .0.data)]
pub struct SyntaxError(pub Locatable<String>);

impl From<Locatable<String>> for CompileError {
    fn from(err: Locatable<String>) -> Self {
        CompileError::Semantic(err)
    }
}

impl From<SyntaxError> for CompileError {
    fn from(err: SyntaxError) -> Self {
        CompileError {
            location: err.0.location,
            data: err.0.data,
        }
    }
}

impl From<Locatable<String>> for SyntaxError {
    fn from(err: Locatable<String>) -> Self {
        Self(err)
    }
}

impl CompileError {
    pub fn location(&self) -> Location {
        match self {
            CompileError::Lex(err) => err.location,
            CompileError::Syntax(err) => err.0.location,
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
