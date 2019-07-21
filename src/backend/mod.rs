use std::cmp::max;
use std::convert::{TryFrom, TryInto};

use inkwell::types::{self, AnyType, AnyTypeEnum, BasicType, BasicTypeEnum, FloatType};
use inkwell::AddressSpace;

use crate::data::Type;
use Type::*;

// NOTE: this is required by the standard to always be one
const CHAR_SIZE: u32 = 1;

// TODO: allow this to be configured at runtime
mod x64;
pub use x64::*;

impl Type {
    pub fn can_represent(&self, other: &Type) -> bool {
        unimplemented!(
            "don't know if {} can represent {}, it's platform dependent",
            self,
            other
        )
    }
    // TODO: instead of doing this manually,
    // convert to LLVM type and call t.size_of()
    pub fn sizeof(&self) -> Result<u32, &'static str> {
        match self {
            Bool => Ok(BOOL_SIZE),
            Char(_) => Ok(CHAR_SIZE),
            Short(_) => Ok(SHORT_SIZE),
            Int(_) => Ok(INT_SIZE),
            Long(_) => Ok(LONG_SIZE),
            Float => Ok(FLOAT_SIZE),
            Double => Ok(DOUBLE_SIZE),
            Pointer(_, _) => Ok(PTR_SIZE),
            // now for the hard ones
            Array(t, l) => t.sizeof().and_then(|n| Ok(n * l.length()?)),
            Enum(symbols) => {
                let uchar = CHAR_BIT as usize;
                // integer division, but taking the ceiling instead of the floor
                // https://stackoverflow.com/a/17974/7669110
                let ubytes = (symbols.len() + uchar - 1) / uchar;
                ubytes
                    .try_into()
                    .map_err(|_| "enum cannot be represented in 32 bits")
            }
            // TODO: this doesn't handle padding
            Union(symbols) => symbols
                .iter()
                .map(|symbol| symbol.ctype.sizeof())
                // max of member sizes
                .try_fold(1, |n, size| Ok(max(n, size?))),
            // TODO: ditto padding
            Struct(symbols) => symbols
                .iter()
                .map(|symbol| symbol.ctype.sizeof())
                // sum of member sizes
                .try_fold(0, |n, size| Ok(n + size?)),
            Bitfield(_) => unimplemented!("sizeof(bitfield)"),
            // illegal operations
            Function(_) => Err("cannot take `sizeof` a function"),
            Void => Err("cannot take `sizeof` void"),
        }
    }
    // TODO: instead of doing this manually,
    // convert to LLVM type and call t.size_of()
    pub fn alignof(&self) -> Result<u32, &'static str> {
        match self {
            Bool
            | Char(_)
            | Short(_)
            | Int(_)
            | Long(_)
            | Float
            | Double
            | Pointer(_, _)
            // TODO: is this correct? still need to worry about padding
            | Union(_)
            | Enum(_)
            | Struct(_) => self.sizeof(),
            Array(t, _) => t.alignof(),
            Bitfield(_) => unimplemented!("alignof bitfield"),
            Function(_) => Err("cannot take `alignof` function"),
            Void => Err("cannot take `alignof` void"),
        }
    }
}

// create a integer type of size `x`
macro_rules! int_width {
    ( $x: expr ) => {
        // see http://llvm.org/doxygen/Type_8cpp_source.html#l00239,
        // if this is a known type it's treated as if we'd gone through the proper function
        Ok(types::IntType::custom_width_int_type($x).as_basic_type_enum())
    };
}

// given an enum $enum with some variants that share a method,
// call that method on each of them
// useful if each variant of an enum has that method but the enum doesn't implement
// a trait giving you access to it
macro_rules! gen_calls {
    // an enum to match and a method to call on all variants
    ( $enum: expr, $method: ident,
      // with arbitrary arguments
      $args: tt,
      // for an arbitrary number of variants
      $( $id: ident ),* ) => {
        match $enum {
            $( $id(t) => t.$method($args), )*
        }
    }
}

trait ToPointerType {
    fn ptr_type(&self, address_space: AddressSpace) -> types::PointerType;
}
trait ToArrayType {
    fn array_type(&self, array_size: u32) -> types::ArrayType;
}
impl ToPointerType for AnyTypeEnum {
    fn ptr_type(&self, addr: AddressSpace) -> types::PointerType {
        use AnyTypeEnum::*;
        gen_calls!(
            self,
            ptr_type,
            addr,
            VoidType,
            PointerType,
            FloatType,
            IntType,
            FunctionType,
            StructType,
            VectorType,
            ArrayType
        )
    }
}
impl ToArrayType for BasicTypeEnum {
    fn array_type(&self, array_size: u32) -> types::ArrayType {
        use BasicTypeEnum::*;
        gen_calls!(
            self,
            array_type,
            array_size,
            PointerType,
            FloatType,
            IntType,
            StructType,
            VectorType,
            ArrayType
        )
    }
}

impl TryFrom<Type> for types::BasicTypeEnum {
    type Error = String;
    fn try_from(ty: Type) -> Result<Self, Self::Error> {
        match ty {
            Bool => int_width!(BOOL_SIZE),
            Char(_) => int_width!(CHAR_SIZE),
            Short(_) => int_width!(SHORT_SIZE),
            Int(_) => int_width!(INT_SIZE),
            Long(_) => int_width!(LONG_SIZE),
            Enum(_) => int_width!(ty.sizeof()?),

            // TODO: this is hard-coded for x64 because LLVM doesn't allow specifying a
            // custom type
            Float => Ok(FloatType::f32_type().as_basic_type_enum()),
            Double => Ok(FloatType::f64_type().as_basic_type_enum()),

            // derived types
            Pointer(t, _) => Ok(AnyTypeEnum::try_from(*t)?
                .ptr_type(AddressSpace::Generic)
                .as_basic_type_enum()),
            Array(t, l) => Ok(BasicTypeEnum::try_from(*t)?
                .array_type(l.length()?)
                .as_basic_type_enum()),
            Struct(members) => {
                let llvm_elements: Vec<BasicTypeEnum> = members
                    .into_iter()
                    .map(|m| m.ctype.try_into())
                    .collect::<Result<_, Self::Error>>()?;
                // TODO: allow struct packing
                Ok(types::StructType::struct_type(&llvm_elements, false).as_basic_type_enum())
            }
            // LLVM does not have a union type.
            // What Clang does is cast it to the type of the largest member,
            // and then cast every element of the union as it is accessed.
            // See https://stackoverflow.com/questions/19549942/extracting-a-value-from-an-union#19550613
            Union(members) => try_max_by_key(members.into_iter().map(|m| m.ctype), Type::sizeof)
                .expect("parser should ensure all unions have at least one member")?
                .try_into(),
            Void | Bitfield(_) | Function(_) => Err(format!("{} is not a basic type", ty)),
        }
    }
}

impl TryFrom<Type> for AnyTypeEnum {
    type Error = String;
    fn try_from(ty: Type) -> Result<AnyTypeEnum, Self::Error> {
        match ty {
            // basic types (according to LLVM)
            Bool
            | Char(_)
            | Short(_)
            | Int(_)
            | Long(_)
            | Enum(_)
            | Float
            | Double
            | Pointer(_, _)
            | Array(_, _)
            | Struct(_)
            | Union(_) => Ok(types::BasicTypeEnum::try_from(ty)?.as_any_type_enum()),
            // any type
            Void => Ok(types::VoidType::void_type().as_any_type_enum()),
            Function(_) => unimplemented!("functions to LLVM type"),
            //Function(func_type) => Ok(types::BasicTypeEnum::try_from(ty)?.func_type())
            // It looks like LLVM has a bitfield type but it isn't exposed by the
            // Inkwell API? See https://stackoverflow.com/questions/25058213/how-to-spot-a-bit-field-with-clang
            Bitfield(_) => unimplemented!("bitfield to llvm type"),
        }
    }
}

/// partially taken from
/// https://doc.rust-lang.org/src/core/iter/traits/iterator.rs.html#2591
/// short-circuiting version of iter.max_by_key
fn try_max_by_key<I, T, C, R, F>(mut iter: I, mut f: F) -> Option<Result<T, R>>
where
    I: Iterator<Item = T>,
    C: std::cmp::Ord,
    F: FnMut(&T) -> Result<C, R>,
{
    iter.next().map(|initial| {
        // if this gives an error, return it immediately
        // avoids f not being called if there's only one element
        f(&initial)?;
        iter.try_fold(initial, |current, next| {
            if f(&current)? >= f(&next)? {
                Ok(current)
            } else {
                Ok(next)
            }
        })
    })
}
