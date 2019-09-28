use std::collections::HashMap;

use super::{Qualifiers, Symbol};
use crate::backend::SIZE_T;

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Type {
    Void,
    Bool,
    Char(bool), // signed or unsigned
    Short(bool),
    Int(bool),
    Long(bool),
    Float,
    Double,
    Pointer(Box<Type>, Qualifiers),
    Array(Box<Type>, ArrayType),
    Function(FunctionType),
    // name, members
    // no members means a tentative definition (struct s;)
    Union(StructType),
    Struct(StructType),
    // enums should always have members, since tentative definitions are not allowed
    Enum(Option<String>, Vec<(String, i64)>),
    Bitfield(Vec<BitfieldType>),
    VaList,
}

/// Structs can be either named or anonymous.
/// Anonymous structs carry all their information with them,
/// there's no need (or way) to use tag_scope.
/// Named structs can have forward declarations and be defined at any point
/// in the program. In order to support self referential structs, named structs
/// do NOT contain a list of their members, only the information that the
/// backend needs to compile them.
///
/// The parser has access to a `tag_scope` that allows it to update the named
/// structs as necessary.
///
/// WARNING: because the parser returns declarations eagerly, it may return a
/// struct that has not yet been defined. This may be fixed at some point in
/// the future. Until then, all consumers are stuck. See
/// https://github.com/jyn514/rcc/issues/44 for an example of how this can manifest.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum StructType {
    // name, size, alignment, offsets
    Named(String, u64, u64, HashMap<String, u64>),
    Anonymous(Vec<Symbol>),
}

#[derive(Clone, Debug)]
pub enum ArrayType {
    Fixed(SIZE_T),
    Unbounded,
}

#[derive(Clone, Debug, Eq)]
// note: old-style declarations are not supported at this time
pub struct FunctionType {
    // why Symbol instead of Type?
    // 1. we need to know qualifiers for the params. if we made that part of Type,
    //    we'd need qualifiers for every step along the way
    //    (consider that int a[][][] parses as 4 nested types).
    // 2. when we do scoping, we need to know the names of formal parameters
    //    (as opposed to concrete arguments).
    //    this is as good a place to store them as any.
    pub return_type: Box<Type>,
    pub params: Vec<Symbol>,
    pub varargs: bool,
}

#[allow(dead_code)]
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct BitfieldType {
    pub offset: i32,
    pub name: Option<String>,
    pub ctype: Type,
}

impl Type {
    /// https://stackoverflow.com/questions/14821936/what-is-a-scalar-object-in-c#14822074
    #[inline]
    pub fn is_scalar(&self) -> bool {
        use Type::*;
        match self {
            Enum(_, _) => true,
            k if k.is_arithmetic() || k.is_pointer() => true,
            _ => false,
        }
    }
    #[inline]
    pub fn is_bool(&self) -> bool {
        match self {
            Type::Bool => true,
            _ => false,
        }
    }
    #[inline]
    pub fn is_char(&self) -> bool {
        match self {
            Type::Char(true) => true,
            _ => false,
        }
    }
    #[inline]
    // returns whether `self` is a signed integer type
    pub fn is_signed(&self) -> bool {
        use Type::*;
        match self {
            Bool | Char(true) | Short(true) | Int(true) | Long(true) | Enum(_, _) => true,
            _ => false,
        }
    }
    #[inline]
    pub fn is_integral(&self) -> bool {
        use Type::*;
        match self {
            Bool | Char(_) | Short(_) | Int(_) | Long(_) | Enum(_, _) => true,
            _ => false,
        }
    }
    #[inline]
    pub fn is_floating(&self) -> bool {
        match self {
            Type::Float | Type::Double => true,
            _ => false,
        }
    }
    #[inline]
    pub fn is_arithmetic(&self) -> bool {
        self.is_integral() || self.is_floating()
    }
    #[inline]
    pub fn is_pointer(&self) -> bool {
        match self {
            Type::Pointer(_, _) => true,
            _ => false,
        }
    }
    #[inline]
    pub fn is_void_pointer(&self) -> bool {
        match self {
            Type::Pointer(t, _) => **t == Type::Void,
            _ => false,
        }
    }
    #[inline]
    /// used for pointer addition and subtraction, see section 6.5.6 of the C11 standard
    pub fn is_pointer_to_complete_object(&self) -> bool {
        match self {
            Type::Pointer(ctype, _) => ctype.is_complete() && !ctype.is_function(),
            _ => false,
        }
    }
    pub fn is_complete(&self) -> bool {
        match self {
            Type::Void | Type::Array(_, ArrayType::Unbounded) => false,
            // TODO: update when we allow incomplete struct and union types (e.g. `struct s;`)
            _ => true,
        }
    }
    #[inline]
    pub fn is_function(&self) -> bool {
        match self {
            Type::Function(_) => true,
            _ => false,
        }
    }
}

impl PartialEq for ArrayType {
    fn eq(&self, _: &Self) -> bool {
        true
    }
}
impl Eq for ArrayType {}

impl PartialEq for FunctionType {
    fn eq(&self, other: &Self) -> bool {
        // no prototype: any parameters are allowed
        // TODO: issue a warning if a function has empty parameters, it's a holdover
        // from C89
        self.params.is_empty()
            || other.params.is_empty()
            || self.varargs == other.varargs
            && self.return_type == other.return_type
            // don't require parameter names and storage_class to match
            && self.params
                .iter()
                .zip(other.params.iter())
                .all(|(this_param, other_param)| {
                    this_param.ctype == other_param.ctype
                        && this_param.qualifiers == other_param.qualifiers
                })
    }
}

impl std::fmt::Display for Type {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        use Type::*;
        match self {
            Char(signed) | Short(signed) | Int(signed) | Long(signed) => {
                let lower = &format!("{:?}", self).to_lowercase();
                let substr = match lower.find('(') {
                    Some(n) => &lower[..n],
                    None => lower.as_str(),
                };
                write!(f, "{}{}", if *signed { "" } else { "unsigned " }, substr)
            }
            Bool | Float | Double | Void => write!(f, "{}", format!("{:?}", self).to_lowercase()),
            Pointer(to, _) => {
                to.print_pre(f)?;
                self.print_mid(f)?;
                to.print_post(f)
            }
            Array(of, _) => {
                of.print_pre(f)?;
                of.print_mid(f)?;
                self.print_post(f)
            }
            Function(FunctionType { return_type, .. }) => {
                write!(f, "{}", return_type)?;
                self.print_post(f)
            }
            Enum(Some(ident), _) => write!(f, "enum {}", ident),
            Enum(None, _) => write!(f, "<anonymous enum>"),
            Union(StructType::Named(ident, _, _, _)) => write!(f, "union {}", ident),
            Union(_) => write!(f, "<anonymous union>"),
            Struct(StructType::Named(ident, _, _, _)) => write!(f, "struct {}", ident),
            Struct(_) => write!(f, "<anonymous struct>"),
            Bitfield(_) => unimplemented!("printing bitfield type"),
            VaList => write!(f, "va_list"),
        }
    }
}

use std::fmt::{self, Formatter};
impl Type {
    fn print_pre(&self, f: &mut Formatter) -> fmt::Result {
        match self {
            Type::Pointer(t, _) | Type::Array(t, _) => t.print_pre(f),
            Type::Function(func_type) => std::fmt::Display::fmt(&func_type.return_type, f),
            _ => write!(f, "{}", self),
        }
    }
    fn print_mid(&self, f: &mut Formatter) -> fmt::Result {
        match self {
            Type::Pointer(to, quals) => {
                to.print_mid(f)?;
                let ptr_description = match (quals.c_const, quals.volatile) {
                    (true, true) => "const volatile ",
                    (true, false) => "const ",
                    (false, true) => "volatile ",
                    (false, false) => "",
                };
                match &**to {
                    Type::Array(_, _) | Type::Function(_) => write!(f, "(*{})", ptr_description),
                    _ => write!(f, " *{}", ptr_description),
                }
            }
            Type::Array(to, _) => to.print_mid(f),
            _ => Ok(()),
        }
    }
    fn print_post(&self, f: &mut Formatter) -> fmt::Result {
        match self {
            Type::Array(to, size) => {
                write!(f, "[")?;
                if let ArrayType::Fixed(size) = size {
                    write!(f, "{}", size)?;
                }
                write!(f, "]")?;
                to.print_post(f)
            }
            Type::Function(func_type) => {
                // https://stackoverflow.com/a/30325430
                let mut comma_seperated = "(".to_string();
                for param in &func_type.params {
                    comma_seperated.push_str(&param.ctype.to_string());
                    comma_seperated.push_str(", ");
                }
                if func_type.varargs {
                    comma_seperated.push_str("...");
                } else if !func_type.params.is_empty() {
                    comma_seperated.pop();
                    comma_seperated.pop();
                }
                comma_seperated.push(')');
                write!(f, "{}", comma_seperated)
            }
            _ => Ok(()),
        }
    }
}

impl FunctionType {
    pub fn should_return(&self) -> bool {
        *self.return_type != Type::Void
    }
    pub fn has_params(&self) -> bool {
        !(self.params.len() == 1 && self.params[0].ctype == Type::Void)
    }
}
