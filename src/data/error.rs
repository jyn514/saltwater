use std::collections::VecDeque;
use std::fmt;
use thiserror::Error;

use super::{Locatable, Location};

/// RecoverableResult is a type that represents a Result that can be recovered from.
///
/// See the [`Recover`] trait for more information.
///
/// [`Recover`]: trait.Recover.html
pub type RecoverableResult<T, E = CompileError> = Result<T, (E, T)>;
pub type CompileResult<T> = Result<T, CompileError>;
pub type SemanticError = Locatable<String>;
pub type CompileError = Locatable<Error>;

/// ErrorHandler is a struct that hold errors generated by the compiler
///
/// An error handler is used because multiple errors may be generated by each
/// part of the compiler, this cannot be represented well with Rust's normal
/// `Result`.
#[derive(Debug, Default, PartialEq)]
pub(crate) struct ErrorHandler {
    errors: VecDeque<CompileError>,
}

impl ErrorHandler {
    /// Construct a new error handler.
    pub(crate) fn new() -> ErrorHandler {
        Default::default()
    }

    /// Add an error to the error handler.
    pub(crate) fn push_back<E: Into<CompileError>>(&mut self, error: E) {
        self.errors.push_back(error.into());
    }

    pub(crate) fn pop_front(&mut self) -> Option<CompileError> {
        self.errors.pop_front()
    }

    /// Checks if there are errors in the handler
    pub(crate) fn is_empty(&self) -> bool {
        self.errors.is_empty()
    }
}

impl IntoIterator for ErrorHandler {
    type Item = CompileError;
    type IntoIter = <VecDeque<CompileError> as IntoIterator>::IntoIter;

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

pub(crate) trait Recover {
    type Ok;
    fn recover(self, error_handler: &mut ErrorHandler) -> Self::Ok;
}

impl<T, E: Into<CompileError>> Recover for RecoverableResult<T, E> {
    type Ok = T;
    fn recover(self, error_hander: &mut ErrorHandler) -> T {
        self.unwrap_or_else(|(e, i)| {
            error_hander.push_back(e.into());
            i
        })
    }
}

impl<T, E: Into<CompileError>> Recover for RecoverableResult<T, Vec<E>> {
    type Ok = T;
    fn recover(self, error_handler: &mut ErrorHandler) -> T {
        self.unwrap_or_else(|(es, i)| {
            for e in es {
                error_handler.push_back(e.into());
            }
            i
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn new_error(error: Error) -> CompileError {
        CompileError::new(error, Location::default())
    }

    #[test]
    fn test_error_handler_push_err() {
        let mut error_handler = ErrorHandler::new();
        error_handler.push_back(new_error(Error::UnterminatedComment));

        assert_eq!(
            error_handler,
            ErrorHandler {
                errors: vec_deque![new_error(Error::UnterminatedComment)]
            }
        );
    }

    #[test]
    fn test_error_handler_into_iterator() {
        let mut error_handler = ErrorHandler::new();
        error_handler.push_back(new_error(Error::GenericSemantic("stuff".to_string())));
        let errors = error_handler.into_iter().collect::<Vec<_>>();
        assert_eq!(errors.len(), 1);
    }

    #[test]
    fn test_error_kind() {
        assert_eq!(Error::GenericLex("".to_string()).kind(), ErrorKind::Lex);
        assert_eq!(
            Error::GenericSemantic("".to_string()).kind(),
            ErrorKind::Semantic
        );
        assert_eq!(
            Error::GenericSyntax("".to_string()).kind(),
            ErrorKind::Syntax
        );
        assert_eq!(Error::UnterminatedComment.kind(), ErrorKind::Lex);
    }

    #[test]
    fn test_compile_error_semantic() {
        assert_eq!(
            CompileError::semantic(Locatable::new("".to_string(), Location::default())),
            new_error(Error::GenericSemantic("".to_string()))
        );
    }

    #[test]
    fn test_compile_error_is_kind() {
        let e = new_error(Error::GenericLex("".to_string()));
        assert!(e.is_lex_err());
        assert!(!e.is_semantic_err());
        assert!(!e.is_syntax_err());

        let e = new_error(Error::GenericSemantic("".to_string()));
        assert!(!e.is_lex_err());
        assert!(e.is_semantic_err());
        assert!(!e.is_syntax_err());

        let e = new_error(Error::GenericSyntax("".to_string()));
        assert!(!e.is_lex_err());
        assert!(!e.is_semantic_err());
        assert!(e.is_syntax_err());
    }

    #[test]
    fn test_compile_error_display() {
        assert_eq!(
            format!("{}", new_error(Error::UnterminatedComment)),
            "invalid token: unterminated /* comment"
        );

        assert_eq!(
            format!(
                "{}",
                new_error(Error::GenericSemantic("bad code".to_string()))
            ),
            "invalid program: bad code"
        );
    }

    #[test]
    fn test_compile_error_from_locatable_string() {
        let e = CompileError::from(Locatable::new("apples".to_string(), Location::default()));
        assert_eq!(e, new_error(Error::GenericSemantic("apples".to_string())));
    }

    #[test]
    fn test_compile_error_from_syntax_error() {
        let e = CompileError::from(SyntaxError(Locatable::new(
            "oranges".to_string(),
            Location::default(),
        )));
        assert_eq!(e, new_error(Error::GenericSyntax("oranges".to_string())));
    }

    #[test]
    fn test_recover_error() {
        let mut error_handler = ErrorHandler::new();
        let r: RecoverableResult<i32> = Ok(1);
        assert_eq!(r.recover(&mut error_handler), 1);
        assert!(error_handler.is_empty());

        let mut error_handler = ErrorHandler::new();
        let r: RecoverableResult<i32> = Err((new_error(Error::UnterminatedComment), 42));
        assert_eq!(r.recover(&mut error_handler), 42);
        let errors = error_handler.into_iter().collect::<Vec<_>>();
        assert_eq!(errors, vec![new_error(Error::UnterminatedComment)]);
    }

    #[test]
    fn test_recover_multiple_errors() {
        let mut error_handler = ErrorHandler::new();
        let r: RecoverableResult<i32, Vec<CompileError>> = Ok(1);
        assert_eq!(r.recover(&mut error_handler), 1);
        assert!(error_handler.is_empty());

        let mut error_handler = ErrorHandler::new();
        let r: RecoverableResult<i32, Vec<CompileError>> = Err((
            vec![
                new_error(Error::UnterminatedComment),
                new_error(Error::GenericSemantic("pears".to_string())),
            ],
            42,
        ));
        assert_eq!(r.recover(&mut error_handler), 42);
        let errors = error_handler.into_iter().collect::<Vec<_>>();
        assert_eq!(
            errors,
            vec![
                new_error(Error::UnterminatedComment),
                new_error(Error::GenericSemantic("pears".to_string())),
            ]
        );
    }
}
