#![warn(missing_docs)]

use std::cmp::max;

use target_lexicon::Triple;

use crate::data::{
    types::{ArrayType, StructType},
    *,
};
use Type::*;

/// Size of a `char` in bytes
///
/// Note: The standard requires this to always be one.
/// http://port70.net/~nsz/c/c11/n1570.html#6.5.3.5
const CHAR_SIZE: u16 = 1;

pub(crate) trait Arch {
    fn size_max(&self) -> u64;

    fn float_size(&self) -> u16;
    fn double_size(&self) -> u16;

    fn long_size(&self) -> u16;
    fn int_size(&self) -> u16;
    fn short_size(&self) -> u16;
    fn bool_size(&self) -> u16;

    // number of bits in a byte
    fn char_bit(&self) -> u16;
}

impl Arch for Triple {
    fn size_max(&self) -> u64 {
        std::u64::MAX
    }

    fn float_size(&self) -> u16 {
        4
    }
    fn double_size(&self) -> u16 {
        8
    }

    fn long_size(&self) -> u16 {
        8
    }
    fn int_size(&self) -> u16 {
        4
    }
    fn short_size(&self) -> u16 {
        2
    }
    fn bool_size(&self) -> u16 {
        1
    }

    // number of bits in a byte
    fn char_bit(&self) -> u16 {
        8
    }
}

impl StructType {
    /// Get the offset of the given struct member.
    pub(crate) fn offset(&self, member: InternedStr, target: &Triple) -> u64 {
        let members = self.members();
        let mut current_offset = 0;
        for formal in members.iter() {
            if formal.id == member {
                return current_offset;
            }
            current_offset = Self::next_offset(current_offset, &formal.ctype, target)
                .expect("structs should have valid size and alignment");
        }
        unreachable!("cannot call struct_offset for member not in struct");
    }
    /// Get the offset of the next struct member given the current offset.
    fn next_offset(
        mut current_offset: u64,
        ctype: &Type,
        target: &Triple,
    ) -> Result<u64, &'static str> {
        let align = ctype.alignof(target)?;
        // round up to the nearest multiple of align
        let rem = current_offset % align;
        if rem != 0 {
            // for example: 7%4 == 3; 7 + ((4 - 3) = 1) == 8; 8 % 4 == 0
            current_offset += align - rem;
        }
        Ok(current_offset + ctype.sizeof(target)?)
    }
    /// Calculate the size of a struct: the sum of all member sizes
    pub(crate) fn struct_size(&self, target: &Triple) -> Result<u64, &'static str> {
        let symbols = &self.members();

        symbols
            .iter()
            .try_fold(0, |offset, symbol| {
                Ok(StructType::next_offset(offset, &symbol.ctype, target)?)
            })
            .and_then(|size_t| {
                let align_minus_one = self.align(target)? - 1;

                // Rounds up to the next multiple of `align`
                Ok((size_t + align_minus_one) & !align_minus_one)
            })
    }
    /// Calculate the size of a union: the max of all member sizes
    pub(crate) fn union_size(&self, target: &Triple) -> Result<u64, &'static str> {
        let symbols = &self.members();
        symbols
            .iter()
            .map(|symbol| symbol.ctype.sizeof(target))
            // max of member sizes
            .try_fold(1, |n, size| Ok(max(n, size?)))
    }
    /// Calculate the alignment of a struct: the max of all member alignments
    pub(crate) fn align(&self, target: &Triple) -> Result<u64, &'static str> {
        let members = &self.members();
        members.iter().try_fold(0, |max, member| {
            Ok(std::cmp::max(member.ctype.alignof(target)?, max))
        })
    }
}

impl Type {
    /// Returns true if `other` can be converted to `self` without losing infomation.
    pub fn can_represent(&self, other: &Type, target: &Triple) -> bool {
        let (self_size, other_size) = (self.sizeof(target), other.sizeof(target));
        self == other
            || *self == Type::Double && *other == Type::Float
            || (self.is_integral() && other.is_integral())
                && (self_size > other_size
                    || self_size == other_size && self.is_signed() == other.is_signed())
    }

    /// Get the size of a type in bytes.
    ///
    /// This is the `sizeof` operator in C.
    pub fn sizeof(&self, target: &Triple) -> Result<u64, &'static str> {
        match self {
            Bool => Ok(target.bool_size().into()),
            Char(_) => Ok(CHAR_SIZE.into()),
            Short(_) => Ok(target.short_size().into()),
            Int(_) => Ok(target.int_size().into()),
            Long(_) => Ok(target.long_size().into()),
            Float => Ok(target.float_size().into()),
            Double => Ok(target.double_size().into()),
            Pointer(_, _) => Ok(target.pointer_width().unwrap().bytes().into()),
            // now for the hard ones
            Array(t, ArrayType::Fixed(l)) => t
                .sizeof(target)
                .and_then(|n| n.checked_mul(*l).ok_or("overflow in array size")),
            Array(_, ArrayType::Unbounded) => Err("cannot take sizeof variable length array"),
            Enum(_, symbols) => {
                let uchar = target.char_bit() as usize;
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
            Union(struct_type) => struct_type.union_size(target),
            Struct(struct_type) => struct_type.struct_size(target),
            // illegal operations
            Function(_) => Err("cannot take `sizeof` a function"),
            Void => Err("cannot take `sizeof` void"),
            VaList => Err("cannot take `sizeof` va_list"),
            Error => Err("cannot take `sizeof` <type error>"),
        }
    }
    /// Get the alignment of a type in bytes.
    pub fn alignof(&self, target: &Triple) -> Result<u64, &'static str> {
        match self {
            Bool
            | Char(_)
            | Short(_)
            | Int(_)
            | Long(_)
            | Float
            | Double
            | Pointer(_, _)
            | Enum(_, _) => self.sizeof(target),
            Array(t, _) => t.alignof(target),
            // Clang uses the largest alignment of any element as the alignment of the whole
            // Not sure why, but who am I to argue
            // Anyway, Faerie panics if the alignment isn't a power of two so it's probably for the best
            Union(struct_type) | Struct(struct_type) => struct_type.align(target),
            Function(_) => Err("cannot take `alignof` function"),
            Void => Err("cannot take `alignof` void"),
            VaList => Err("cannot take `alignof` va_list"),
            Error => Err("cannot take `alignof` <type error>"),
        }
    }
}

#[cfg(test)]
mod tests {
    use proptest::prelude::*;
    use target_lexicon::HOST;

    use crate::data::{
        hir::Metadata,
        hir::Qualifiers,
        types::{tests::arb_type, StructType, Type},
        StorageClass,
    };

    use super::*;

    fn type_for_size(size: u16) -> Type {
        // TODO: this is hopelessly broken on x32
        match size {
            0 => Type::Void,
            1 => Type::Bool,
            2 => Type::Short(true),
            4 => Type::Int(true),
            8 => Type::Long(true),
            _ => struct_for_types(vec![Type::Char(true); size as usize]),
        }
    }

    fn symbol_for_type(ctype: Type, id: InternedStr) -> Metadata {
        Metadata {
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
        assert_eq!(struct_type.offset(member, &Triple::host()), offset);
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
            let align = type_for_size(size).alignof(&Triple::host()).unwrap();
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
        assert_eq!(char_struct.alignof(&Triple::host()).unwrap(), 1);
        assert_offset(vec![Type::Int(true), Type::Char(true)], 1, 4);
        assert_eq!(char_struct.sizeof(&Triple::host()).unwrap(), 5);
    }
    #[test]
    fn align_of_non_char_struct() {
        let ty = struct_for_types(vec![
            Pointer(Box::new(Int(true)), Qualifiers::default()),
            Int(true),
        ]);
        assert_eq!(ty.alignof(&HOST), Ok(8));
    }

    proptest! {
        // https://github.com/jyn514/rcc/pull/325#issuecomment-596297785
        // prop_assert_eq!(discriminant(&t.sizeof()), discriminant(&t.alignof()));

        #[test]
        fn proptest_align_power_of_two(t in arb_type()) {
            if let Ok(align) = t.alignof(&HOST) {
                prop_assert!(align.is_power_of_two());
            }
        }

        #[test]
        fn proptest_sizeof_multiple_of_alignof(t in arb_type()) {
            if let Ok(sizeof) = t.sizeof(&HOST) {
                prop_assert_eq!(sizeof % t.alignof(&HOST).unwrap(), 0);
            }
        }
    }
}
