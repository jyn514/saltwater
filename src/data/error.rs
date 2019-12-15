use std::fmt;
use thiserror::Error;

use super::{Expr, Locatable, Location};

pub type RecoverableResult<T = Expr, E = CompileError> = Result<T, (E, T)>;
pub type CompileResult<T> = Result<T, Box<dyn NewCompileError>>;
pub type SemanticError = Locatable<String>;

#[derive(Debug, PartialEq, Eq, Error)]
pub enum CompileError {
    #[error("invalid token: {}", .0.data)]
    Lex(Locatable<String>),
    #[error("invalid syntax: {}", (.0).0.data)]
    Syntax(#[from] SyntaxError),
    #[error("invalid program: {}", .0.data)]
    Semantic(Locatable<String>),
}

#[derive(Debug, PartialEq, Eq, Error)]
#[error("{}", .0.data)]
pub struct SyntaxError(pub Locatable<String>);

impl From<Locatable<String>> for CompileError {
    fn from(err: Locatable<String>) -> Self {
        CompileError::Semantic(err)
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

pub enum CompileErrorLevel {
    Warning,
    RecoverableError,
    FatalError,
}

pub trait NewCompileError {
    // Idealy this should be an associated constant, but those are not allowed
    // in trait objects
    fn level(&self) -> CompileErrorLevel;

    // Could also be an associated const
    fn name(&self) -> &'static str;

    fn message(&self) -> String;
    fn location(&self) -> Location;
}

impl fmt::Debug for (dyn NewCompileError) {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}: {}", self.name(), self.message())
    }
}

impl PartialEq for (dyn NewCompileError) {
    fn eq(&self, other: &Self) -> bool {
        self.name() == other.name()
    }
}

impl fmt::Display for (dyn NewCompileError) {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{} ({})", self.message(), self.name())
    }
}

macro_rules! define_error {
    ($error_short_name:expr, $error_level:expr, $error_name:ident($($arg_name:ident: $arg_type:ty ),*), $message:expr) => {
        #[derive(Debug)]
        pub struct $error_name {
            location: Location,
            $($arg_name: $arg_type),*
        }

        impl $error_name {
            pub fn new(location: Location, $($arg_name: $arg_type),*) -> $error_name {
                $error_name { location, $($arg_name),* }
            }
        }

        impl NewCompileError for $error_name {
            fn name(&self) -> &'static str {
                $error_short_name
            }

            fn level(&self) -> CompileErrorLevel {
                $error_level
            }

            fn message(&self) -> String {
                format!($message, $($arg_name = self.$arg_name),*)
            }

            fn location(&self) -> Location {
                self.location
            }
        }
    }
}

pub mod errors {
    use super::*;

    define_error! {
        "error", CompileErrorLevel::FatalError,
        GenericError(message: String),
        "error: {message}"
    }

    define_error! {
        "lex-error", CompileErrorLevel::FatalError,
        GenericLexError(token: String),
        "invalid token: {token}"
    }

    define_error! {
        "syntax-error", CompileErrorLevel::FatalError,
        GenericSyntaxError(message: String),
        "invalid syntax: {message}"
    }

    define_error! {
        "symantic-error", CompileErrorLevel::RecoverableError,
        GenericSemanticError(message: String),
        "invalid program: {message}"
    }

    define_error! {
        "warning", CompileErrorLevel::Warning,
        GenericWarning(message: String),
        "warning: {message}"
    }
}

#[deprecated]
impl From<CompileError> for Box<dyn NewCompileError> {
    fn from(err: CompileError) -> Box<dyn NewCompileError> {
        match err {
            CompileError::Lex(l) => Box::new(errors::GenericLexError::new(l.location, l.data)),
            CompileError::Syntax(s) => {
                Box::new(errors::GenericSyntaxError::new(s.0.location, s.0.data))
            }
            CompileError::Semantic(l) => {
                Box::new(errors::GenericSemanticError::new(l.location, l.data))
            }
        }
    }
}

#[deprecated]
impl From<SyntaxError> for Box<dyn NewCompileError> {
    fn from(err: SyntaxError) -> Box<dyn NewCompileError> {
        Box::new(errors::GenericSyntaxError::new(err.0.location, err.0.data))
    }
}

#[deprecated]
impl From<Locatable<String>> for Box<dyn NewCompileError> {
    fn from(err: Locatable<String>) -> Box<dyn NewCompileError> {
        Box::new(errors::GenericError::new(err.location, err.data))
    }
}
