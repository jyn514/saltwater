use std::collections::HashMap;
use std::convert::TryFrom;
use std::fmt::{self, Display, Formatter};

#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum Keyword {
    // keywords
    If,
    Else,
    Do,
    While,
    For,
    Switch,
    Case,
    Default,
    Break,
    Continue,
    Return,
    Goto,

    // types
    Bool,
    Char,
    Short,
    Int,
    Long,
    Float,
    Double,
    Void,
    Signed,
    Unsigned,
    Typedef,
    Union,
    Struct,

    // qualifiers
    Const,
    Volatile,

    // storage classes
    Auto,
    Register,
    Static,
    Extern,

    Sizeof,
}

#[derive(Clone, Debug, PartialEq)]
pub enum Token {
    PlusPlus,
    MinusMinus,

    PlusEqual,
    MinusEqual,
    StarEqual,
    DivideEqual,
    ModEqual,
    LeftEqual,  // <<=
    RightEqual, // >>=
    AndEqual,
    OrEqual,
    XorEqual, // ^=

    EqualEqual,
    NotEqual,
    LessEqual,
    GreaterEqual,

    Plus,
    Minus,
    Star,
    Divide,
    Mod,
    Xor,
    Equal,
    Less,
    Greater,
    Ampersand,
    LogicalAnd,
    BinaryOr,
    LogicalOr,
    BinaryNot,  // ~
    LogicalNot, // !
    ShiftRight,
    ShiftLeft,

    LeftBrace, // {
    RightBrace,
    LeftBracket, // [
    RightBracket,
    LeftParen,
    RightParen,
    Semicolon,
    Colon,
    Comma,
    Dot,
    Question,

    // literals
    Int(i64),
    Float(f64),
    Str(String),
    Char(char),
    Id(String),

    Keyword(Keyword),

    // Misc
    Ellipsis,
    StructDeref, // ->
}

#[derive(Clone, Debug, PartialEq)]
pub enum Stmt {
    Compound(Vec<Stmt>),
    If(Expr, Box<Stmt>, Option<Box<Stmt>>),
    Do(Box<Stmt>, Expr),
    While(Expr, Option<Box<Stmt>>),
    For(Box<Stmt>, Expr, Box<Stmt>, Box<Stmt>),
    Switch(Expr, Box<Stmt>),
    Label(String, Option<Box<Stmt>>),
    Case(Expr),
    Default,
    Expr(Expr),
    Goto(String),
    Continue,
    Break,
    Return(Option<Expr>),
}

#[derive(Clone, Debug)]
pub struct Declaration {
    pub symbol: Symbol,
    pub init: Option<Initializer>,
}

#[derive(Clone, Debug, PartialEq)]
pub enum Initializer {
    Scalar(Expr),                      // int i = 5;
    CompoundStatement(Vec<Stmt>),      // int f() { return 0; }
    InitializerList(Vec<Initializer>), // int a[] = { 1, 2, 3 };
}

/// Holds the metadata for an expression.
///
/// This should be the datatype you use in APIs, etc.
/// because it is more useful than the raw ExprType.
#[derive(Clone, Debug, PartialEq)]
pub struct Expr {
    /// expr: holds the actual expression
    pub expr: ExprType,

    /// ctype: holds the type of the expression
    pub ctype: Type,

    /// constexpr: whether a value can be constant-folded at compile-time
    ///
    /// unrelated to the `const` keyword
    /// NOTE: can sometimes be true at the same time as `lval` (e.g. for constant arrays)
    pub constexpr: bool,

    /// lval: whether an expression can be assigned to
    ///
    /// for example, variables, array elements, and pointer dereferences are lvals,
    /// but literals, functions, and addresses cannot
    pub lval: bool,

    /// location: the best approximation of where the expression is
    ///
    /// usually points to the location of the operation symbol, or the literal if no
    /// operations is being performed
    /// implicit operations should point to the child expression
    pub location: Location,
}

#[derive(Clone, Debug, PartialEq)]
pub enum ExprType {
    Id(Symbol),
    Literal(Token),
    Array(Box<Expr>, Box<Expr>),
    FuncCall(Box<Expr>, Vec<Expr>),
    Member(Box<Expr>, Token),
    // pre/post inc/dec-rement
    Increment(Box<Expr>, bool, bool),
    Cast(Box<Expr>, Type),
    Sizeof(Type),
    Ref(Box<Expr>),
    Deref(Box<Expr>),
    Negate(Box<Expr>),
    LogicalNot(Box<Expr>),
    BitwiseNot(Box<Expr>),
    LogicalOr(Box<Expr>, Box<Expr>),
    BitwiseOr(Box<Expr>, Box<Expr>),
    LogicalAnd(Box<Expr>, Box<Expr>),
    BitwiseAnd(Box<Expr>, Box<Expr>),
    Xor(Box<Expr>, Box<Expr>),
    Mul(Box<Expr>, Box<Expr>),
    Div(Box<Expr>, Box<Expr>),
    Mod(Box<Expr>, Box<Expr>),
    Add(Box<Expr>, Box<Expr>),
    Sub(Box<Expr>, Box<Expr>),
    // bool: left or right
    Shift(Box<Expr>, Box<Expr>, bool),
    // Token: make >, <, <=, ... part of the same variant
    Compare(Box<Expr>, Box<Expr>, Token),
    // Token: allow extended assignment
    Assign(Box<Expr>, Box<Expr>, Token),
    // Ternary: if ? then : else
    Ternary(Box<Expr>, Box<Expr>, Box<Expr>),
    Comma(Box<Expr>, Box<Expr>),
}

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
    Union(Vec<Symbol>),
    Struct(Vec<Symbol>),
    Function(FunctionType),
    Enum(Vec<String>),
    Bitfield(Vec<BitfieldType>),
}

#[derive(Clone, Debug)]
pub enum ArrayType {
    Fixed(Box<Expr>),
    Unbounded,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum StorageClass {
    Static = Keyword::Static as isize,
    Extern = Keyword::Extern as isize,
    Auto = Keyword::Auto as isize,
    Register = Keyword::Register as isize,
}

/* structs */
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Symbol {
    pub id: String,
    pub ctype: Type,
    pub qualifiers: Qualifiers,
    pub storage_class: StorageClass,
    pub init: bool,
}

#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct Qualifiers {
    pub volatile: bool,
    pub c_const: bool,
}

#[derive(Clone, Debug, PartialEq, Eq)]
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

#[derive(Clone, Debug, Default, PartialEq)]
pub struct Scope {
    parent: Option<Box<Scope>>,
    variables: HashMap<String, Symbol>,
}

// holds where a piece of code came from
// should almost always be immutable
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct Location {
    // if there's a 4 GB input file, we have bigger problems
    pub line: u32,
    pub column: u32,
    pub file: String,
}

#[derive(Clone, Debug)]
pub struct Locatable<T> {
    pub data: T,
    pub location: Location,
}

/* impls */
impl<T: PartialEq> PartialEq for Locatable<T> {
    fn eq(&self, other: &Self) -> bool {
        self.data == other.data
    }
}

impl<T: Eq> Eq for Locatable<T> {}

#[allow(dead_code)]
impl Qualifiers {
    pub const NONE: Qualifiers = Qualifiers {
        c_const: false,
        volatile: false,
    };
    pub const VOLATILE: Qualifiers = Qualifiers {
        c_const: false,
        volatile: true,
    };
    pub const CONST: Qualifiers = Qualifiers {
        c_const: true,
        volatile: false,
    };
    pub const CONST_VOLATILE: Qualifiers = Qualifiers {
        c_const: true,
        volatile: true,
    };
}

lazy_static! {
    pub static ref INT_POINTER: Type =
        { Type::Pointer(Box::new(Type::Int(true)), Qualifiers::NONE) };
}
impl Type {
    /// https://stackoverflow.com/questions/14821936/what-is-a-scalar-object-in-c#14822074
    #[inline]
    pub fn is_scalar(&self) -> bool {
        use Type::*;
        match self {
            Enum(_) => true,
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
    pub fn is_integral(&self) -> bool {
        use Type::*;
        match self {
            Bool | Char(_) | Short(_) | Int(_) | Long(_) => true,
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
    pub fn is_function(&self) -> bool {
        match self {
            Type::Function(_) => true,
            _ => false,
        }
    }
}

pub enum LengthError {
    Unbounded,
    Dynamic,
    NonIntegral,
}

impl ArrayType {
    pub fn length(&self) -> Result<u32, LengthError> {
        match self {
            ArrayType::Unbounded => Err(LengthError::Unbounded),
            ArrayType::Fixed(expr) => {
                if !expr.ctype.is_integral() {
                    return Err(LengthError::NonIntegral);
                }
                unimplemented!("constant folding and dynamic array length");
            }
        }
    }
}

impl From<LengthError> for String {
    fn from(err: LengthError) -> String {
        let s: &'static str = err.into();
        s.to_string()
    }
}

impl From<LengthError> for &'static str {
    fn from(err: LengthError) -> &'static str {
        use LengthError::*;
        match err {
            Unbounded => "Cannot take the length of unbounded array type",
            Dynamic => "Length of variable-length array cannot be known at compile time",
            NonIntegral => "The length of an array must be an integer",
        }
    }
}

impl Scope {
    pub fn new() -> Scope {
        Scope {
            parent: None,
            variables: HashMap::new(),
        }
    }
    pub fn with_parent(parent: Scope) -> Scope {
        Scope {
            parent: Some(Box::new(parent)),
            variables: HashMap::new(),
        }
    }
    pub fn discard(self) -> Option<Scope> {
        self.parent.map(|p| *p)
    }
    pub fn get(&self, name: &str) -> Option<&Symbol> {
        let immediate = self.get_immediate(name);
        if let Some(parent) = &self.parent {
            immediate.or_else(|| parent.get(name))
        } else {
            immediate
        }
    }
    // returns whether the _immediate_ scope contains `name`
    pub fn insert(&mut self, symbol: Symbol) -> Option<Symbol> {
        self.variables.insert(symbol.id.clone(), symbol)
    }
    pub fn get_immediate(&self, name: &str) -> Option<&Symbol> {
        self.variables.get(name)
    }
}

pub fn zero() -> Expr {
    Expr {
        ctype: Type::Int(true),
        constexpr: true,
        expr: ExprType::Literal(Token::Int(0)),
        lval: false,
        location: Default::default(),
    }
}

impl TryFrom<Keyword> for StorageClass {
    type Error = Keyword;
    fn try_from(value: Keyword) -> Result<StorageClass, Keyword> {
        use StorageClass::*;
        match value {
            Keyword::Extern => Ok(Extern),
            Keyword::Static => Ok(Static),
            Keyword::Auto => Ok(Auto),
            Keyword::Register => Ok(Register),
            _ => Err(value),
        }
    }
}

impl Default for StorageClass {
    fn default() -> StorageClass {
        StorageClass::Auto
    }
}

impl Display for Keyword {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        write!(f, "{}", &format!("{:?}", self).to_lowercase())
    }
}

impl Display for StorageClass {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        write!(f, "{}", &format!("{:?}", self).to_lowercase())
    }
}

impl Display for Type {
    // TODO: this will break badly for anything that's not a primitive
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
            Pointer(to, Qualifiers { c_const, volatile }) => write!(
                f,
                "*{}{}",
                match (c_const, volatile) {
                    (true, true) => "const volatile ",
                    (true, false) => "const ",
                    (false, true) => "volatile ",
                    (false, false) => "",
                },
                to,
            ),
            Array(of, size) => write!(
                f,
                "{}[{}]",
                of,
                match size {
                    // TODO: don't use debug formatting here
                    ArrayType::Fixed(expr) => format!("{:?}", expr),
                    ArrayType::Unbounded => String::new(),
                }
            ),
            Function(FunctionType {
                return_type,
                params,
                varargs,
            }) => {
                write!(f, "{}", return_type)?;
                // https://stackoverflow.com/a/30325430
                let mut comma_seperated = " (".to_string();
                for param in params {
                    comma_seperated.push_str(&param.ctype.to_string());
                    comma_seperated.push_str(", ");
                }
                if *varargs {
                    comma_seperated.push_str("...");
                } else if !params.is_empty() {
                    comma_seperated.pop();
                    comma_seperated.pop();
                }
                comma_seperated.push(')');
                write!(f, "{}", comma_seperated)
            }
            Union(_) | Struct(_) | Enum(_) | Bitfield(_) => unimplemented!(),
        }
    }
}

impl Display for Token {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        use Token::*;
        match self {
            PlusPlus => write!(f, "++"),
            PlusEqual => write!(f, "+="),
            MinusMinus => write!(f, "--"),
            MinusEqual => write!(f, "+="),
            StarEqual => write!(f, "*="),
            DivideEqual => write!(f, "/="),
            ModEqual => write!(f, "%="),
            AndEqual => write!(f, "&="),
            OrEqual => write!(f, "|="),
            XorEqual => write!(f, "^="),
            LeftEqual => write!(f, "<<="),
            RightEqual => write!(f, ">>="),
            EqualEqual => write!(f, "=="),
            NotEqual => write!(f, "!="),
            LessEqual => write!(f, "<="),
            GreaterEqual => write!(f, ">="),
            ShiftRight => write!(f, ">>"),
            ShiftLeft => write!(f, "<<"),
            Plus => write!(f, "+"),
            Minus => write!(f, "-"),
            Star => write!(f, "*"),
            Divide => write!(f, "/"),
            Xor => write!(f, "^"),
            Equal => write!(f, "="),
            Less => write!(f, "<"),
            Greater => write!(f, ">"),
            Ampersand => write!(f, "&"),
            LogicalAnd => write!(f, "&&"),
            BinaryOr => write!(f, "|"),
            LogicalOr => write!(f, "||"),
            BinaryNot => write!(f, "~"),
            LogicalNot => write!(f, "!"),
            LeftBrace => write!(f, "{{"),
            RightBrace => write!(f, "}}"),
            LeftBracket => write!(f, "["),
            RightBracket => write!(f, "]"),
            LeftParen => write!(f, "("),
            RightParen => write!(f, ")"),
            Semicolon => write!(f, ";"),
            Colon => write!(f, ":"),
            Comma => write!(f, ","),
            Dot => write!(f, "."),
            Question => write!(f, "?"),
            Mod => write!(f, "%"),

            Int(i) => write!(f, "{}", i),
            Float(n) => write!(f, "{}", n),
            Str(s) => write!(f, "\"{}\"", s),
            Char(c) => write!(f, "{}", c),
            Id(id) => write!(f, "{}", id),
            Keyword(k) => write!(f, "{}", k),

            Ellipsis => write!(f, "..."),
            StructDeref => write!(f, "->"),
        }
    }
}

impl PartialEq for ArrayType {
    fn eq(&self, _: &Self) -> bool {
        true
    }
}
impl Eq for ArrayType {}
