use std::cmp::max;
use std::convert::TryInto;

use cranelift::codegen::{
    ir::{
        types::{self, Type as IrType},
        AbiParam, Signature,
    },
    isa::CallConv,
};
use target_lexicon::Triple;

use crate::data::{ArrayType, FunctionType, Locatable, Location, Type};
use Type::*;

// NOTE: this is required by the standard to always be one
const CHAR_SIZE: u16 = 1;

// TODO: allow this to be configured at runtime
lazy_static! {
    // TODO: make this `const` when
    // https://github.com/CraneStation/target-lexicon/pull/19 is merged
    pub static ref TARGET: Triple = Triple::host();
    pub static ref CALLING_CONVENTION: CallConv = CallConv::triple_default(&TARGET);
}
mod x64;
pub use x64::*;

impl Type {
    pub fn can_represent(&self, other: &Type) -> bool {
        self == other
            || *self == Type::Double && *other == Type::Float
            || (self.is_integral() && other.is_integral())
                && (self.sizeof() > other.sizeof()
                    || self.sizeof() == other.sizeof() && self.is_signed() == other.is_signed())
    }

    // TODO: instead of doing this manually,
    // convert to LLVM type and call t.size_of()
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
    pub fn ptr_type() -> IrType {
        IrType::int(CHAR_BIT * PTR_SIZE).expect("pointer size should be valid")
    }
    pub fn as_ir_basic_type(&self) -> Result<IrType, String> {
        match self {
            // Integers
            Bool => Ok(types::B1),
            Char(_) | Short(_) | Int(_) | Long(_) | Pointer(_, _) | Enum(_) => {
                let int_size = SIZE_T::from(CHAR_BIT)
                    * self
                        .sizeof()
                        .expect("integers should always have a valid size");
                Ok(IrType::int(int_size.try_into().unwrap_or_else(|_| {
                    panic!(
                        "integers should never have a size larger than {}",
                        i16::max_value()
                    )
                }))
                .unwrap_or_else(|| panic!("unsupported size for IR: {}", int_size)))
            }

            // Floats
            // TODO: this is hard-coded for x64 because LLVM doesn't allow specifying a
            // custom type
            Float => Ok(types::F32),
            Double => Ok(types::F64),

            // Aggregates
            // arrays decay to pointers at the assembly level
            Array(_, _) => Ok(IrType::int(PTR_SIZE * CHAR_BIT)
                .unwrap_or_else(|| panic!("unsupported size of IR: {}", PTR_SIZE))),
            Struct(members) => {
                let llvm_elements: Vec<_> = members
                    .iter()
                    .map(|m| m.ctype.as_ir_basic_type())
                    .collect::<Result<_, String>>()?;
                // need to figure out how padding works
                unimplemented!("struct type -> IR");
            }
            // LLVM does not have a union type.
            // What Clang does is cast it to the type of the largest member,
            // and then cast every element of the union as it is accessed.
            // See https://stackoverflow.com/questions/19549942/extracting-a-value-from-an-union#19550613
            Union(members) => try_max_by_key(members.iter().map(|m| &m.ctype), Type::sizeof)
                .expect("parser should ensure all unions have at least one member")?
                .as_ir_basic_type(),
            Bitfield(_) => unimplemented!("bitfield to llvm type"),
            Void | Function(_) => Err(format!("{} is not a basic type", self)),
        }
    }
    pub fn as_ir_type(&self) -> Result<IrType, String> {
        match self {
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
            | Bitfield(_)
            | Union(_) => self.as_ir_basic_type(),
            // void cannot be loaded or stored
            Void => Ok(types::INVALID),
            // I don't think Cranelift IR has a representation for functions
            Function(_) => unimplemented!("functions to LLVM type"),
            //Function(func_type) => Ok(ty.to_llvm_basic()?.func_type())
        }
    }
}

impl FunctionType {
    pub fn signature(&self, location: &Location) -> Result<Signature, Locatable<String>> {
        let params = if self.params.len() == 1 && self.params[0].ctype == Type::Void {
            // no arguments
            Vec::new()
        } else {
            self.params
                .iter()
                .map(|param| {
                    param
                        .ctype
                        .as_ir_basic_type()
                        .map(AbiParam::new)
                        .map_err(|err| Locatable {
                            data: err,
                            location: location.clone(),
                        })
                })
                .collect::<Result<Vec<_>, Locatable<String>>>()?
        };
        let return_type = if !self.should_return() {
            vec![]
        } else {
            vec![self
                .return_type
                .as_ir_basic_type()
                .map(AbiParam::new)
                .map_err(|err| Locatable {
                    data: err,
                    location: location.clone(),
                })?]
        };
        Ok(Signature {
            call_conv: *CALLING_CONVENTION,
            params,
            returns: return_type,
        })
    }
}

/// short-circuiting version of iter.max_by_key
///
/// partially taken from https://doc.rust-lang.org/src/core/iter/traits/iterator.rs.html#2591
///
/// Example:
///
/// ```
/// use rcc::backend::try_max_by_key;
/// let list = [[1, 2, 3], [5, 4, 3], [1, 1, 4]];
/// assert_eq!(try_max_by_key(list.iter(), |vec| vec.last().map(|&x| x).ok_or(())), Some(Ok(&[1, 1, 4])));
///
/// let lengths = [vec![], vec![1], vec![1, 2]];
/// assert_eq!(try_max_by_key(lengths.iter(), |vec| vec.last().map(|&x| x).ok_or(())), Some(Err(())));
/// ```
pub fn try_max_by_key<'a, I, T, C, R, F>(mut iter: I, mut f: F) -> Option<Result<&'a T, R>>
where
    I: Iterator<Item = &'a T>,
    C: std::cmp::Ord,
    F: FnMut(&T) -> Result<C, R>,
{
    iter.next().map(|initial| {
        // if this gives an error, return it immediately
        // avoids f not being called if there's only one element
        f(&initial)?;
        iter.try_fold(initial, |current, next| {
            if f(current)? >= f(next)? {
                Ok(current)
            } else {
                Ok(next)
            }
        })
    })
}
