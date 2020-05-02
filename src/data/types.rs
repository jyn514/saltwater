use super::hir::{Metadata, MetadataRef};
use crate::intern::InternedStr;
#[cfg(test)]
use proptest_derive::Arbitrary;
use std::fmt::{self, Formatter};
pub use struct_ref::{StructRef, StructType};
use target_lexicon::Triple;

mod struct_ref {
    use std::cell::RefCell;
    use std::rc::Rc;

    use super::Metadata;

    thread_local!(
        /// The global storage for all struct definitions.
        ///
        /// The type is read like so:
        /// RefCell: A container with interior mutability, used because `LocalKey`
        /// returns an immutable reference.
        /// Vec: A growable list of definitions.
        /// Rc: A hack so that the members can be accessed across function boundaries,
        /// see the documentation for `StructRef::get`.
        /// Vec<Symbol>: The members of a single struct definition.
        static TYPES: RefCell<Vec<Rc<Vec<Metadata>>>> = Default::default()
    );

    /// A reference to a struct definition. Allows self-referencing structs.
    #[derive(Copy, Clone, Debug, Eq)]
    pub struct StructRef(usize);

    impl PartialEq for StructRef {
        fn eq(&self, other: &Self) -> bool {
            // see if we can do this the cheap way first;
            // otherwise fall back to comparing every member
            self.0 == other.0 || self.get() == other.get()
        }
    }

    impl Default for StructRef {
        fn default() -> Self {
            Self::new()
        }
    }

    impl StructRef {
        /// Create a reference to a new struct.
        pub fn new() -> StructRef {
            TYPES.with(|list| {
                let mut types = list.borrow_mut();
                let index = types.len();
                types.push(Rc::new(vec![]));
                StructRef(index)
            })
        }

        /// Returns the definition for a given struct.
        ///
        /// Examples:
        /// ```
        /// use rcc::data::types::StructRef;
        /// let struct_ref = StructRef::new();
        /// let members = struct_ref.get();
        /// for symbol in members.iter() {
        ///     println!("{:?}", symbol);
        /// }
        /// ```
        // Implementation hack: because thread_local items cannot be returned
        // from a closure, this uses an Rc so that it can be `clone`d cheaply.
        // The clone is necessary so the members do not reference TYPES.
        pub fn get(self) -> Rc<Vec<Metadata>> {
            TYPES.with(|list| list.borrow()[self.0].clone())
        }

        /// Change the definition for a struct.
        ///
        /// It is a logic error to use this for anything other than defining
        /// forward-declared structs.
        ///
        /// Examples:
        ///
        /// ```compile_fail
        /// use rcc::data::types::StructRef;
        /// let struct_ref = StructRef::new();
        /// struct_ref.update(vec![Symbol::new()]);
        /// ```
        pub(crate) fn update<V>(self, members: V)
        where
            V: Into<Rc<Vec<Metadata>>>,
        {
            TYPES.with(|list| {
                let mut types = list.borrow_mut();
                types[self.0] = members.into();
            });
        }
    }

    /// Structs can be either named or anonymous.
    #[derive(Clone, Debug, PartialEq)]
    pub enum StructType {
        /// Named structs can have forward declarations and be defined at any point
        /// in the program. In order to support self referential structs, named structs
        /// contain an indirect reference to their members, which can be dereferenced with
        /// `StructRef::get`.
        ///
        /// To update a forward declaration, use `StructRef::update`.
        Named(super::InternedStr, StructRef),
        /// Anonymous structs carry all their information with them,
        /// there's no need (or way) to use StructRef.
        Anonymous(Rc<Vec<Metadata>>),
    }

    impl StructType {
        /// Get the members of a struct, regardless of which variant it is
        pub fn members(&self) -> Rc<Vec<Metadata>> {
            match self {
                StructType::Anonymous(members) => Rc::clone(members),
                StructType::Named(_, struct_ref) => struct_ref.get(),
            }
        }
        /// Return whether the struct has no members.
        ///
        /// For `Named` structs, this occurs whenever we have seen
        /// a forward declaration but no definition.
        ///
        /// For `Anonymous` structs, this occurs only when there has been a
        /// type error of some sort.
        pub fn is_empty(&self) -> bool {
            match self {
                StructType::Anonymous(members) => members.is_empty(),
                StructType::Named(_, struct_ref) => struct_ref.get().is_empty(),
            }
        }
    }
}

#[derive(Clone, Debug, PartialEq)]
pub enum Type {
    Void,
    Bool,
    Char(bool), // signed or unsigned
    Short(bool),
    Int(bool),
    Long(bool),
    Float,
    Double,
    // TODO: separate Qualifiers into LvalQualifiers and FunctionQualifiers
    Pointer(Box<Type>, super::hir::Qualifiers),
    Array(Box<Type>, ArrayType),
    Function(FunctionType),
    Union(StructType),
    Struct(StructType),
    /// Enums should always have members, since tentative definitions are not allowed
    Enum(Option<InternedStr>, Vec<(InternedStr, i64)>),
    /// This is the type used for variadic arguments.
    VaList,
    /// A semantic error occured while parsing this type.
    Error,
}

#[derive(Clone, Debug, PartialEq, Eq)]
#[cfg_attr(test, derive(Arbitrary))]
pub enum ArrayType {
    Fixed(u64),
    Unbounded,
}

// NOTE: K&R declarations are not supported at this time
#[derive(Clone, Debug)]
pub struct FunctionType {
    // TODO: allow FunctionQualifiers as well
    pub return_type: Box<Type>,
    // why Metadata instead of Type?
    // 1. we need to know qualifiers for the params. if we made that part of Type,
    //    we'd need qualifiers for every step along the way
    //    (consider that int a[][][] parses as 4 nested types).
    // 2. when we do scoping, we need to know the names of formal parameters
    //    (as opposed to concrete arguments).
    //    this is as good a place to store them as any.
    pub params: Vec<MetadataRef>,
    pub varargs: bool,
}

impl Type {
    /// https://stackoverflow.com/questions/14821936/what-is-a-scalar-object-in-c#14822074
    #[inline]
    pub(crate) fn is_scalar(&self) -> bool {
        use Type::*;
        match self {
            Enum(_, _) => true,
            k if k.is_arithmetic() || k.is_pointer() => true,
            _ => false,
        }
    }
    #[inline]
    pub(crate) fn is_bool(&self) -> bool {
        match self {
            Type::Bool => true,
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
    pub(crate) fn is_arithmetic(&self) -> bool {
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
    pub fn is_function(&self) -> bool {
        match self {
            Type::Function(_) => true,
            _ => false,
        }
    }
    pub(crate) fn member_offset(&self, member: InternedStr, target: &Triple) -> Result<u64, ()> {
        match self {
            Type::Struct(stype) => Ok(stype.offset(member, target)),
            Type::Union(_) => Ok(0),
            _ => Err(()),
        }
    }
}

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
                .all(|(a, b)| {
                    let (this_param, other_param) = (a.get(), b.get());
                    this_param.ctype == other_param.ctype
                        && this_param.qualifiers == other_param.qualifiers
                })
    }
}

impl std::fmt::Display for Type {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        print_type(self, None, f)
    }
}

pub(super) fn print_type(
    ctype: &Type,
    name: Option<InternedStr>,
    f: &mut Formatter,
) -> fmt::Result {
    print_pre(ctype, f)?;
    print_mid(ctype, name, f)?;
    print_post(ctype, f)
}

fn print_pre(ctype: &Type, f: &mut Formatter) -> fmt::Result {
    use Type::*;
    match ctype {
        Char(signed) | Short(signed) | Int(signed) | Long(signed) => {
            let lower = &format!("{:?}", ctype).to_lowercase();
            let substr = match lower.find('(') {
                Some(n) => &lower[..n],
                None => lower.as_str(),
            };
            write!(f, "{}{}", if *signed { "" } else { "unsigned " }, substr)
        }
        Bool => write!(f, "_Bool"),
        Float | Double | Void => write!(f, "{}", format!("{:?}", ctype).to_lowercase()),
        Pointer(inner, _) | Array(inner, _) => print_pre(inner, f),
        Function(ftype) => print_type(&ftype.return_type, None, f),
        Enum(Some(ident), _) => write!(f, "enum {}", ident),
        Enum(None, _) => write!(f, "<anonymous enum>"),
        Union(StructType::Named(ident, _)) => write!(f, "union {}", ident),
        Union(_) => write!(f, "<anonymous union>"),
        Struct(StructType::Named(ident, _)) => write!(f, "struct {}", ident),
        Struct(_) => write!(f, "<anonymous struct>"),
        VaList => write!(f, "va_list"),
        Error => write!(f, "<type error>"),
    }
}

fn print_mid(ctype: &Type, name: Option<InternedStr>, f: &mut Formatter) -> fmt::Result {
    match ctype {
        Type::Pointer(to, qs) => {
            let name = name.unwrap_or_default();
            // what do we do for (**p)()?
            // we have to look arbitrarily deep into the type,
            // but also we have to only print the ( once,
            // so how do we know we know if it's already been printed?
            let depth = match &**to {
                Type::Array(_, _) | Type::Function(_) => true,
                _ => false,
            };
            print_mid(to, None, f)?;

            write!(f, " ")?;
            if depth {
                write!(f, "(")?;
            }

            let pointer = if qs != &Default::default() && name != InternedStr::default() {
                format!("*{} {}", qs, name)
            } else {
                format!("*{}{}", qs, name)
            };
            write!(f, "{}", pointer)?;
            if depth {
                write!(f, ")")?;
            }
            Ok(())
        }
        Type::Array(to, _) => print_mid(to, name, f),
        _ => {
            if let Some(name) = name {
                write!(f, " {}", name)?;
            }
            Ok(())
        }
    }
}
fn print_post(ctype: &Type, f: &mut Formatter) -> fmt::Result {
    match ctype {
        Type::Pointer(to, _) => print_post(to, f),
        Type::Array(to, size) => {
            write!(f, "[")?;
            if let ArrayType::Fixed(size) = size {
                write!(f, "{}", size)?;
            }
            write!(f, "]")?;
            print_post(to, f)
        }
        Type::Function(func_type) => {
            write!(f, "(")?;
            let mut params = func_type.params.iter();
            let print = |f: &mut _, symbol: MetadataRef| {
                let symbol = symbol.get();
                let id = if symbol.id == InternedStr::default() {
                    None
                } else {
                    Some(symbol.id)
                };
                print_type(&symbol.ctype, id, f)
            };
            if let Some(&first) = params.next() {
                print(f, first)?;
            }
            for &symbol in params {
                write!(f, ", ")?;
                print(f, symbol)?;
            }
            if func_type.varargs {
                write!(f, ", ...")?;
            }
            write!(f, ")")
        }
        _ => Ok(()),
    }
}

impl FunctionType {
    pub(crate) fn should_return(&self) -> bool {
        *self.return_type != Type::Void
    }
}

#[cfg(test)]
pub(crate) mod tests {
    use proptest::prelude::*;

    use super::{ArrayType, InternedStr, Type};
    use crate::data::hir::Qualifiers;

    pub(crate) fn arb_type() -> impl Strategy<Value = Type> {
        let leaf = prop_oneof![
            Just(Type::Void),
            Just(Type::Bool),
            any::<bool>().prop_map(Type::Char),
            any::<bool>().prop_map(Type::Short),
            any::<bool>().prop_map(Type::Int),
            any::<bool>().prop_map(Type::Long),
            Just(Type::Float),
            Just(Type::Double),
            // enum
            any::<(Option<InternedStr>, Vec<(InternedStr, i64)>)>()
                .prop_map(|(name, members)| Type::Enum(name, members)),
            Just(Type::VaList),
            Just(Type::Error),
        ];

        leaf.prop_recursive(8, 256, 10, |inner| {
            prop_oneof![
                (inner.clone(), any::<Qualifiers>())
                    .prop_map(|(t, q)| Type::Pointer(Box::new(t), q)),
                (inner, any::<ArrayType>()).prop_map(|(t, at)| Type::Array(Box::new(t), at)),
                //Type::Function(FunctionType),
                //Type::Union(StructType),
                //Type::Struct(StructType),
            ]
        })
    }
}
