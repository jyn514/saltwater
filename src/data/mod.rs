pub mod ast;
pub mod error;
pub mod hir;
pub mod lex;
pub mod types;

pub use crate::intern::InternedStr;
pub(crate) use error::ErrorHandler;
pub use error::{CompileError, CompileResult, CompileWarning, Error, SemanticError, SyntaxError};
pub use hir::LiteralValue;
pub use lex::{LiteralToken, Locatable, Location, Token};
pub use types::Type;
pub use types::{StructRef, StructType};

use std::convert::TryFrom;
use std::fmt::{self, Display};

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
    it: I,
    delim: &str,
) -> String {
    joined(it.into_iter().map(|s| s.data.to_string()), delim)
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Radix {
    Binary,
    Octal,
    Decimal,
    Hexadecimal,
}

impl Radix {
    pub fn as_u8(self) -> u8 {
        match self {
            Radix::Binary => 2,
            Radix::Octal => 8,
            Radix::Decimal => 10,
            Radix::Hexadecimal => 16,
        }
    }
}

impl Display for Radix {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let word = match self {
            Radix::Binary => "binary",
            Radix::Octal => "octal",
            Radix::Decimal => "decimal",
            Radix::Hexadecimal => "hexadecimal",
        };
        write!(f, "{}", word)
    }
}

impl TryFrom<u32> for Radix {
    type Error = ();
    fn try_from(int: u32) -> Result<Radix, ()> {
        match int {
            2 => Ok(Radix::Binary),
            8 => Ok(Radix::Octal),
            10 => Ok(Radix::Decimal),
            16 => Ok(Radix::Hexadecimal),
            _ => Err(()),
        }
    }
}

/*
#[cfg(test)]
mod tests {
    use crate::analyze::test::analyze;
    use crate::Parser;

    #[test]
    fn type_display() {
        let types = [
            "int",
            "int *",
            "int [1][2][3]",
            "char *(*)(float)",
            "short *(*)[1][2][3]",
            "_Bool",
            "struct s",
        ];
        for ty in types.iter() {
            let parsed_ty = analyze(ty, |x| Parser::type_name(x, &[]), |a, (b, _)| {
                a.parse_typename_test(b.data, b.location)
            })
            .unwrap();
            assert_eq!(&parsed_ty.to_string(), *ty);
        }
    }
}
*/
