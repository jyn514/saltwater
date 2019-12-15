use std::any::Any;
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

#[derive(PartialEq, Debug)]
pub enum ErrorKind {
    Warning,
    Lex,
    Semantic,
    Syntax,
}

pub trait NewCompileError: Any {
    // Idealy this should be an associated constant, but those are not allowed
    // in trait objects
    fn kind(&self) -> ErrorKind;

    // Could also be an associated const
    fn name(&self) -> &'static str;

    fn message(&self) -> String;
    fn location(&self) -> Location;
}

impl dyn NewCompileError {
    pub fn is<T: NewCompileError>(&self) -> bool {
        use std::any::TypeId;
        let t = TypeId::of::<T>();
        let boxed = self.type_id();
        t == boxed
    }

    // TODO: Possibly add a downcast function
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

// The ergonomics of this macro needs improvement.
macro_rules! define_error {
    ($error_short_name:expr, $error_kind:expr, $error_name:ident($($arg_name:ident: $arg_type:ty ),*), $message:expr) => {
        #[derive(Debug)]
        pub struct $error_name {
            location: Location,
            $($arg_name: $arg_type),*
        }

        impl $error_name {
            // Having this defer to a normal constructor might be useful
            pub fn boxed(location: Location, $($arg_name: $arg_type),*) -> Box<dyn NewCompileError> {
                Box::new($error_name { location, $($arg_name),* })
            }
        }

        impl NewCompileError for $error_name {
            fn name(&self) -> &'static str {
                $error_short_name
            }

            fn kind(&self) -> ErrorKind {
                $error_kind
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
        "lex-error", ErrorKind::Lex,
        GenericLexError(token: String),
        "invalid token: {token}"
    }

    define_error! {
        "syntax-error", ErrorKind::Syntax,
        GenericSyntaxError(message: String),
        "invalid syntax: {message}"
    }

    define_error! {
        "semantic-error", ErrorKind::Semantic,
        GenericSemanticError(message: String),
        "invalid program: {message}"
    }

    define_error! {
        "warning", ErrorKind::Warning,
        GenericWarning(message: String),
        "warning: {message}"
    }
}

// These two Into implementations shoul be phased out soon (see issue #156)
impl From<CompileError> for Box<dyn NewCompileError> {
    fn from(err: CompileError) -> Box<dyn NewCompileError> {
        match err {
            CompileError::Lex(l) => errors::GenericLexError::boxed(l.location, l.data),
            CompileError::Syntax(s) => errors::GenericSyntaxError::boxed(s.0.location, s.0.data),
            CompileError::Semantic(l) => errors::GenericSemanticError::boxed(l.location, l.data),
        }
    }
}

impl From<SyntaxError> for Box<dyn NewCompileError> {
    fn from(err: SyntaxError) -> Box<dyn NewCompileError> {
        errors::GenericSyntaxError::boxed(err.0.location, err.0.data)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_error_trait() {
        #[allow(unreachable_pub)]
        mod test_errors {
            use super::*;

            define_error! {
                "test-error", ErrorKind::Semantic,
                TestError(message: String),
                "test-error: {message}"
            }

            define_error! {
                "test-warning", ErrorKind::Warning,
                TestWarning(number: i32),
                "test-warning data: {number:x}"
            }
        }

        let e = test_errors::TestError::boxed(Location::default(), "bad stuff happened".into());
        assert!(e.is::<test_errors::TestError>());
        assert!(!e.is::<test_errors::TestWarning>());
        assert_eq!(e.kind(), ErrorKind::Semantic);
        assert_eq!(e.name(), "test-error");
        assert_eq!(e.message(), "test-error: bad stuff happened");
        assert_eq!(e.location(), Location::default());

        let w = test_errors::TestWarning::boxed(Location::default(), 32);
        assert!(w.is::<test_errors::TestWarning>());
        assert!(!w.is::<test_errors::TestError>());
        assert_eq!(w.kind(), ErrorKind::Warning);
        assert_eq!(w.name(), "test-warning");
        assert_eq!(w.message(), "test-warning data: 20");
        assert_eq!(w.location(), Location::default());
    }
}
