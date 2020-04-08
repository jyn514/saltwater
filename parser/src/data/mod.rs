pub mod ast;
pub mod error;
pub mod hir;
pub mod lex;
pub mod types;

pub use crate::intern::InternedStr;
pub use error::{CompileError, CompileResult, CompileWarning, Error, SemanticError, SyntaxError};
pub(crate) use error::{ErrorHandler, Recover, RecoverableResult};
pub use lex::{DefaultLocation as Location, Literal, Locatable, LocationTrait, Token};
pub use types::Type;
pub use types::{StructRef, StructType};

use lex::Keyword;

// used by both `ast` and `hir`
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum StorageClass {
    Static,
    Extern,
    Auto,
    Register,
    Typedef,
}

// helper functions for `Display` impls
fn joined<I: IntoIterator<Item = T>, T: ToString>(it: I, delim: &str) -> String {
    it.into_iter()
        .map(|s| s.to_string())
        .collect::<Vec<_>>()
        .join(delim)
}

fn joined_locatable<'a, I: IntoIterator<Item = &'a Locatable<T>>, T: ToString + 'a>(
    it: I, delim: &str,
) -> String {
    joined(it.into_iter().map(|s| s.data.to_string()), delim)
}
