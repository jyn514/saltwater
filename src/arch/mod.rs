#![warn(missing_docs)]

use std::cmp::max;
use std::convert::TryInto;

use cranelift::codegen::{
    ir::{
        types::{self, Type as IrType},
        AbiParam, ArgumentPurpose, Signature,
    },
    isa::{CallConv, TargetIsa},
};
use lazy_static::lazy_static;
use target_lexicon::Triple;

use crate::data::{
    types::{ArrayType, FunctionType, StructType},
    *,
};
use Type::*;

/// Size of a `char` in bytes
///
/// Note: The standard requires this to always be one.
/// http://port70.net/~nsz/c/c11/n1570.html#6.5.3.5
const CHAR_SIZE: u16 = 1;

// TODO: allow this to be configured at runtime
/// The target triple for the host.
///
/// A "target triple" is used to represent information about a compiler target.
/// Traditionaly, the target triple uses this format: `<architecture>-<vendor>-<operating system>`
/// The target triple is represented as a struct and contains additional
/// information like ABI and endianness.
pub(crate) const TARGET: Triple = Triple::host();

// TODO: make this const when const_if_match is stabilized
// TODO: see https://github.com/rust-lang/rust/issues/49146
lazy_static! {
    /// The calling convention for the current target.
    pub(crate) static ref CALLING_CONVENTION: CallConv = CallConv::triple_default(&TARGET);
}

mod x64;
pub(crate) use x64::*;

impl StructType {
    /// Get the offset of the given struct member.
    pub(crate) fn offset(&self, member: InternedStr) -> u64 {
        let members = self.members();
        let mut current_offset = 0;
        for formal in members.iter() {
            if formal.id == member {
                return current_offset;
            }
            current_offset = Self::next_offset(current_offset, &formal.ctype)
                .expect("structs should have valid size and alignment");
        }
        unreachable!("cannot call struct_offset for member not in struct");
    }
    /// Get the offset of the next struct member given the current offset.
    fn next_offset(mut current_offset: u64, ctype: &Type) -> Result<u64, &'static str> {
        let align = ctype.alignof()?;
        // round up to the nearest multiple of align
        let rem = current_offset % align;
        if rem != 0 {
            // for example: 7%4 == 3; 7 + ((4 - 3) = 1) == 8; 8 % 4 == 0
            current_offset += align - rem;
        }
        Ok(current_offset + ctype.sizeof()?)
    }
    /// Calculate the size of a struct: the sum of all member sizes
    pub(crate) fn struct_size(&self) -> Result<SIZE_T, &'static str> {
        let symbols = &self.members();

        symbols
            .iter()
            .try_fold(0, |offset, symbol| {
                Ok(StructType::next_offset(offset, &symbol.ctype)?)
            })
            .and_then(|size_t| {
                let align_minus_one = self.align()? - 1;

                // Rounds up to the next multiple of `align`
                Ok((size_t + align_minus_one) & !align_minus_one)
            })
    }
    /// Calculate the size of a union: the max of all member sizes
    pub(crate) fn union_size(&self) -> Result<SIZE_T, &'static str> {
        let symbols = &self.members();
        symbols
            .iter()
            .map(|symbol| symbol.ctype.sizeof())
            // max of member sizes
            .try_fold(1, |n, size| Ok(max(n, size?)))
    }
    /// Calculate the alignment of a struct: the max of all member alignments
    pub(crate) fn align(&self) -> Result<SIZE_T, &'static str> {
        let members = &self.members();
        members.iter().try_fold(0, |max, member| {
            Ok(std::cmp::max(member.ctype.alignof()?, max))
        })
    }
}

impl Type {
    /// Returns true if `other` can be converted to `self` without losing infomation.
    pub fn can_represent(&self, other: &Type) -> bool {
        self == other
            || *self == Type::Double && *other == Type::Float
            || (self.is_integral() && other.is_integral())
                && (self.sizeof() > other.sizeof()
                    || self.sizeof() == other.sizeof() && self.is_signed() == other.is_signed())
    }

    /// Get the size of a type in bytes.
    ///
    /// This is the `sizeof` operator in C.
    pub fn sizeof(&self) -> Result<SIZE_T, &'static str> {
        match self {
            Bool => Ok(BOOL_SIZE.into()),
            Char(_) => Ok(CHAR_SIZE.into()),
            Short(_) => Ok(SHORT_SIZE.into()),
            Int(_) => Ok(INT_SIZE.into()),
            Long(_) => Ok(LONG_SIZE.into()),
            Float => Ok(FLOAT_SIZE.into()),
            Double => Ok(DOUBLE_SIZE.into()),
            Pointer(_, _) => Ok(PTR_SIZE.into()),
            // now for the hard ones
            Array(t, ArrayType::Fixed(l)) => t.sizeof().and_then(|n| Ok(n * l)),
            Array(_, ArrayType::Unbounded) => Err("cannot take sizeof variable length array"),
            Enum(_, symbols) => {
                let uchar = CHAR_BIT as usize;
                // integer division, but taking the ceiling instead of the floor
                // https://stackoverflow.com/a/17974/7669110
                Ok(match (symbols.len() + uchar - 1) / uchar {
                    0..=8 => 8,
                    9..=16 => 16,
                    17..=32 => 32,
                    33..=64 => 64,
                    _ => return Err("enum cannot be represented in SIZE_T bits"),
                })
            }
            Union(struct_type) => struct_type.union_size(),
            Struct(struct_type) => struct_type.struct_size(),
            // illegal operations
            Function(_) => Err("cannot take `sizeof` a function"),
            Void => Err("cannot take `sizeof` void"),
            VaList => Err("cannot take `sizeof` va_list"),
            Error => Err("cannot take `sizeof` <type error>"),
        }
    }
    /// Get the alignment of a type in bytes.
    pub fn alignof(&self) -> Result<SIZE_T, &'static str> {
        match self {
            Bool
            | Char(_)
            | Short(_)
            | Int(_)
            | Long(_)
            | Float
            | Double
            | Pointer(_, _)
            | Enum(_, _) => self.sizeof(),
            Array(t, _) => t.alignof(),
            // Clang uses the largest alignment of any element as the alignment of the whole
            // Not sure why, but who am I to argue
            // Anyway, Faerie panics if the alignment isn't a power of two so it's probably for the best
            Union(struct_type) | Struct(struct_type) => struct_type.align(),
            Function(_) => Err("cannot take `alignof` function"),
            Void => Err("cannot take `alignof` void"),
            VaList => Err("cannot take `alignof` va_list"),
            Error => Err("cannot take `alignof` <type error>"),
        }
    }
    /// Return an IR integer type large enough to contain a pointer.
    pub fn ptr_type() -> IrType {
        IrType::int(CHAR_BIT * PTR_SIZE).expect("pointer size should be valid")
    }
    /// Return an IR type which can represent this C type
    pub fn as_ir_type(&self) -> IrType {
        match self {
            // Integers
            Bool => types::B1,
            Char(_) | Short(_) | Int(_) | Long(_) | Pointer(_, _) | Enum(_, _) => {
                let int_size = SIZE_T::from(CHAR_BIT)
                    * self
                        .sizeof()
                        .expect("integers should always have a valid size");
                IrType::int(int_size.try_into().unwrap_or_else(|_| {
                    panic!(
                        "integers should never have a size larger than {}",
                        i16::max_value()
                    )
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
}

impl FunctionType {
    /// Generate the IR function signature for `self`
    pub fn signature(&self, isa: &dyn TargetIsa) -> Signature {
        let mut params = if self.params.len() == 1 && self.params[0].ctype == Type::Void {
            // no arguments
            Vec::new()
        } else {
            self.params
                .iter()
                .map(|param| AbiParam::new(param.ctype.as_ir_type()))
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

#[cfg(test)]
mod tests {
    use super::*;
    use crate::data::{
        hir::Metadata as Symbol,
        hir::Qualifiers,
        types::{StructType, Type},
        StorageClass,
    };

    fn type_for_size(size: u16) -> Type {
        match size {
            0 => Type::Void,
            BOOL_SIZE => Type::Bool,
            SHORT_SIZE => Type::Short(true),
            INT_SIZE => Type::Int(true),
            LONG_SIZE => Type::Long(true),
            _ => struct_for_types(vec![Type::Char(true); size as usize]),
        }
    }

    fn symbol_for_type(ctype: Type, id: InternedStr) -> Symbol {
        Symbol {
            id,
            ctype,
            qualifiers: Qualifiers::NONE,
            storage_class: StorageClass::Auto,
        }
    }
    fn struct_for_types(types: Vec<Type>) -> Type {
        let members = {
            let mut v = vec![];
            for (i, ctype) in types.into_iter().enumerate() {
                v.push(symbol_for_type(
                    ctype,
                    InternedStr::get_or_intern(i.to_string()),
                ));
            }
            v
        };
        Type::Struct(StructType::Anonymous(std::rc::Rc::new(members)))
    }
    fn assert_offset(types: Vec<Type>, member_index: usize, offset: u64) {
        let c_type = struct_for_types(types);
        let struct_type = if let Type::Struct(s) = &c_type {
            s
        } else {
            unreachable!()
        };
        let member = (struct_type.members())[member_index].id;
        assert_eq!(struct_type.offset(member), offset);
    }
    #[test]
    fn first_member() {
        for size in 1..128 {
            let types = vec![type_for_size(size)];
            assert_offset(types, 0, 0);
        }
    }
    #[test]
    fn second_member() {
        for size in 1..128 {
            let types = vec![type_for_size(size), Type::Bool];
            assert_offset(types, 1, size.into());
        }
    }
    #[test]
    fn align() {
        for size in 1..128 {
            let align = type_for_size(size).alignof().unwrap();
            assert_eq!(align, align.next_power_of_two());
        }
    }
    #[test]
    fn multiples() {
        let two = type_for_size(2);
        let four = type_for_size(4);
        let eight = type_for_size(8);
        let sixteen = type_for_size(16);
        assert_offset(vec![four, two], 1, 4);
        assert_offset(vec![eight.clone(), sixteen.clone()], 1, 8);
        assert_offset(vec![sixteen.clone(), eight], 1, 16);
        let twenty_four = type_for_size(24);
        assert_offset(vec![twenty_four, sixteen], 1, 24);
    }
    #[test]
    fn char_struct() {
        let char_struct = type_for_size(5);
        assert_eq!(char_struct.alignof().unwrap(), 1);
        assert_offset(vec![Type::Int(true), Type::Char(true)], 1, 4);
        assert_eq!(char_struct.sizeof().unwrap(), 5);
    }
    #[test]
    fn align_of_non_char_struct() {
        let ty = struct_for_types(vec![
            Pointer(Box::new(Int(true)), Qualifiers::default()),
            Int(true),
        ]);
        assert_eq!(ty.alignof(), Ok(8));
    }
}
