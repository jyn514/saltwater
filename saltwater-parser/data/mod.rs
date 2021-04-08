pub mod ast;
pub mod error;
pub mod hir;
pub mod lex;
pub mod types;

pub use crate::intern::InternedStr;
pub use error::{
    CompileError, CompileResult, CompileWarning, Error, ErrorHandler, SemanticError, SyntaxError,
};
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
            let parsed_ty = analyze(ty, Parser::type_name, |a, b| {
                a.parse_typename_test(b.data, b.location)
            })
            .unwrap();
            assert_eq!(&parsed_ty.to_string(), *ty);
        }
    }
}

#[cfg(feature = "codegen")]
mod codegen_impls {
    use crate::arch::*;
    use crate::data::{
        error::CompileError,
        lex::{ComparisonToken, Locatable},
        types::FunctionType,
        Type,
    };
    use crate::intern::InternedStr;
    use cranelift_codegen::ir::Signature;
    use cranelift_codegen::ir::{
        condcodes::{FloatCC, IntCC},
        types::{self, Type as IrType},
        AbiParam, ArgumentPurpose,
    };
    use cranelift_codegen::isa::{CallConv, TargetIsa};

    // TODO: make this const when const_if_match is stabilized
    // TODO: see https://github.com/rust-lang/rust/issues/49146
    lazy_static::lazy_static! {
        /// The calling convention for the current target.
        pub(crate) static ref CALLING_CONVENTION: CallConv = CallConv::triple_default(&TARGET);
    }

    impl FunctionType {
        pub fn should_return(&self) -> bool {
            *self.return_type != Type::Void
        }
    }

    impl Type {
        /// Return an IR integer type large enough to contain a pointer.
        pub fn ptr_type() -> IrType {
            IrType::int(CHAR_BIT * PTR_SIZE).expect("pointer size should be valid")
        }
        /// Return an IR type which can represent this C type
        pub fn as_ir_type(&self) -> IrType {
            use std::convert::TryInto;
            use Type::*;

            match self {
                // Integers
                Bool => types::B1,
                Char(_) | Short(_) | Int(_) | Long(_) | Pointer(_, _) | Enum(_, _) => {
                    let int_size = SIZE_T::from(CHAR_BIT)
                        * self
                            .sizeof()
                            .expect("integers should always have a valid size");
                    IrType::int(int_size.try_into().unwrap_or_else(|_| {
                        panic!("integers should never have a size larger than {}", i16::MAX)
                    }))
                    .unwrap_or_else(|| panic!("unsupported size for IR: {}", int_size))
                }

                // Floats
                // TODO: this is hard-coded for x64
                Float => types::F32,
                Double => types::F64,

                // Aggregates
                // arrays and functions decay to pointers
                Function(_) | Array(_, _) => IrType::int(PTR_SIZE * CHAR_BIT)
                    .unwrap_or_else(|| panic!("unsupported size of IR: {}", PTR_SIZE)),
                // void cannot be loaded or stored
                _ => types::INVALID,
            }
        }
        pub fn member_offset(&self, member: InternedStr) -> Result<u64, ()> {
            match self {
                Type::Struct(stype) => Ok(stype.offset(member)),
                Type::Union(_) => Ok(0),
                _ => Err(()),
            }
        }
    }

    impl CompileError {
        pub fn semantic(err: Locatable<String>) -> Self {
            Self::from(err)
        }
    }

    impl FunctionType {
        pub fn has_params(&self) -> bool {
            !(self.params.len() == 1 && self.params[0].get().ctype == Type::Void)
        }

        /// Generate the IR function signature for `self`
        pub fn signature(&self, isa: &dyn TargetIsa) -> Signature {
            let mut params = if self.params.len() == 1 && self.params[0].get().ctype == Type::Void {
                // no arguments
                Vec::new()
            } else {
                self.params
                    .iter()
                    .map(|param| AbiParam::new(param.get().ctype.as_ir_type()))
                    .collect()
            };
            if self.varargs {
                let al = isa
                    .register_info()
                    .parse_regunit("rax")
                    .expect("x86 should have an rax register");
                params.push(AbiParam::special_reg(
                    types::I8,
                    ArgumentPurpose::Normal,
                    al,
                ));
            }
            let return_type = if !self.should_return() {
                vec![]
            } else {
                vec![AbiParam::new(self.return_type.as_ir_type())]
            };
            Signature {
                call_conv: *CALLING_CONVENTION,
                params,
                returns: return_type,
            }
        }
    }

    impl ComparisonToken {
        pub fn to_int_compare(self, signed: bool) -> IntCC {
            use ComparisonToken::*;
            match (self, signed) {
                (Less, true) => IntCC::SignedLessThan,
                (Less, false) => IntCC::UnsignedLessThan,
                (LessEqual, true) => IntCC::SignedLessThanOrEqual,
                (LessEqual, false) => IntCC::UnsignedLessThanOrEqual,
                (Greater, true) => IntCC::SignedGreaterThan,
                (Greater, false) => IntCC::UnsignedGreaterThan,
                (GreaterEqual, true) => IntCC::SignedGreaterThanOrEqual,
                (GreaterEqual, false) => IntCC::UnsignedGreaterThanOrEqual,
                (EqualEqual, _) => IntCC::Equal,
                (NotEqual, _) => IntCC::NotEqual,
            }
        }
        pub fn to_float_compare(self) -> FloatCC {
            use ComparisonToken::*;
            match self {
                Less => FloatCC::LessThan,
                LessEqual => FloatCC::LessThanOrEqual,
                Greater => FloatCC::GreaterThan,
                GreaterEqual => FloatCC::GreaterThanOrEqual,
                EqualEqual => FloatCC::Equal,
                NotEqual => FloatCC::NotEqual,
            }
        }
    }
}
