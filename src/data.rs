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

    Sizeof
}

#[derive(Clone, Debug, PartialEq)]
pub enum Token {
    PlusPlus,
    PlusEqual,
    MinusMinus,
    MinusEqual,
    DivideEqual,
    EqualEqual,
    NotEqual,
    LessEqual,
    GreaterEqual,
    ShiftRight,
    ShiftLeft,

    Plus,
    Minus,
    Star,
    Divide,
    Mod,
    Equal,
    Not,
    Less,
    Greater,
    Ampersand,
    LogicalAnd,
    BinaryOr,
    LogicalOr,

    LeftBrace,  // {
    RightBrace,
    LeftBracket,  // [
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

    Keyword(Keyword)
}

#[derive(Clone, Debug, PartialEq)]
#[allow(dead_code)]
pub enum Stmt {
    If(Expr, Box<Stmt>, Option<Box<Stmt>>),
    Do(Box<Stmt>, Expr),
    While(Expr, Box<Stmt>),
    For(Box<Stmt>, Expr, Box<Stmt>, Box<Stmt>),
    Switch(Expr, Box<Stmt>),
    Label(String),
    Case(Expr),
    Default,
    Declaration(Symbol),
    ExprStmt(Expr),
    Goto(String),
    Continue,
    Break,
    Return(Expr),
}

#[allow(dead_code)]
#[derive(Clone, Debug, PartialEq)]
pub enum Expr {
    Id(Token),
    Int(Token),
    Float(Token),
    Char(Token),
    Str(Token),
    Array(Box<Expr>, Box<Expr>),
    FuncCall(Box<Expr>, Vec<Expr>),
    Member(Box<Expr>, Token),
    // pre/post inc/dec-rement
    Increment(Box<Expr>, bool, bool),
    Cast(Box<Expr>, Type),
    Sizeof(Box<Expr>),
    Ref(Box<Expr>),
    Deref(Box<Expr>),
    Negate(Box<Expr>),
    LogicalNot(Box<Expr>),
    BitwiseNot(Box<Expr>),
    Mul(Box<Expr>, Box<Expr>),
    Div(Box<Expr>, Box<Expr>),
    Mod(Box<Expr>, Box<Expr>),
    Add(Box<Expr>, Box<Expr>),
    Subtract(Box<Expr>, Box<Expr>),
    // bool: left or right
    Shift(Box<Expr>, Box<Expr>, bool),
    // Token: make >, <, <=, ... part of the same variant
    Compare(Box<Expr>, Box<Expr>, Token),
    // Token: allow extended assignment
    Assign(Box<Expr>, Box<Expr>, Token)
}

#[allow(dead_code)]
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Type {
    Void,
    Char(bool),  // signed or unsigned
    Short(bool),
    Int(bool),
    Long(bool),
    Float,
    Double,
    Pointer(Box<Type>),
    Array(ArrayType),
    Union(Vec<Symbol>),
    Struct(Vec<Symbol>),
    Function(FunctionType),
    Enum(Vec<String>),
    Bitfield(Vec<BitfieldType>)
}

#[allow(dead_code)]
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ArrayType {
    Fixed(i32),
    Unbounded
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum StorageClass {
    Static = Keyword::Static as isize,
    Extern = Keyword::Extern as isize,
    Auto = Keyword::Auto as isize,
    Register = Keyword::Register as isize
}

/* structs */
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Symbol {
    pub id: String,
    pub c_type: Type,
    pub qualifiers: Qualifiers,
    pub storage_class: StorageClass
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Qualifiers {
    pub volatile: bool,
    pub c_const: bool
}

#[allow(dead_code)]
#[derive(Clone, Debug, PartialEq, Eq)]
// note: old-style declarations are not supported at this time
pub struct FunctionType {
    pub return_type: Box<Type>,
    pub params: Vec<Type>,
    pub varargs: bool
}

#[allow(dead_code)]
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct BitfieldType {
    pub offset: i32,
    pub name: Option<String>,
    pub c_type: Type,
}

// holds where a piece of code came from
// should almost always be immutable
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Location<'a> {
    // if there's a 4 GB input file, we have bigger problems
    pub line: u32,
    pub column: u32,
    pub file: &'a str
}

#[derive(Clone, Debug, PartialEq)]
pub struct Locatable<'a, T> {
    pub data: T,
    pub location: Location<'a>
}

/* constants */
#[allow(dead_code)]
impl Qualifiers {
    pub const NONE: Qualifiers = Qualifiers { volatile: false, c_const: false };
    pub const VOLATILE: Qualifiers = Qualifiers { volatile: true, c_const: false };
    pub const CONST: Qualifiers = Qualifiers { volatile: false, c_const: true };
    pub const VOLATILE_CONST: Qualifiers = Qualifiers { volatile: true, c_const: true };
}

/* impls */
impl TryFrom<Keyword> for StorageClass {
    type Error = Keyword;
    fn try_from(value: Keyword) -> Result<StorageClass, Keyword> {
        use StorageClass::*;
        match value {
            Keyword::Extern => Ok(Extern),
            Keyword::Static => Ok(Static),
            Keyword::Auto => Ok(Auto),
            Keyword::Register => Ok(Register),
            _ => Err(value)
        }
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
