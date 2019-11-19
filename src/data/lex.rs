use crate::intern::InternedStr;

// holds where a piece of code came from
// should almost always be immutable
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub struct Location {
    // if there's a 4 GB input file, we have bigger problems
    pub line: u32,
    pub column: u32,
    pub file: InternedStr,
}

#[derive(Clone, Debug)]
pub struct Locatable<T> {
    pub data: T,
    pub location: Location,
}

#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum Keyword {
    // statements
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
    Enum,
    // weird types
    Bool,
    Complex,
    Imaginary,
    VaList,

    // qualifiers
    Const,
    Volatile,
    Restrict,
    // weird qualifiers
    Atomic,
    ThreadLocal,
    // function qualifiers
    Inline,
    NoReturn,

    // storage classes
    Auto,
    Register,
    Static,
    Extern,

    // intrinsics
    Sizeof,
    Generic,
    StaticAssert,
    Alignas,
    Alignof,
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
    BitwiseOr,
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
    UnsignedInt(u64),
    Float(f64),
    Str(InternedStr),
    Char(u8),
    Id(InternedStr),

    Keyword(Keyword),

    // Misc
    Ellipsis,
    StructDeref, // ->
}

/* impls */
impl<T: PartialEq> PartialEq for Locatable<T> {
    fn eq(&self, other: &Self) -> bool {
        self.data == other.data
    }
}

impl<T: Eq> Eq for Locatable<T> {}
impl<T> Locatable<T> {
    pub fn new(data: T, location: Location) -> Self {
        Self { data, location }
    }
}

use cranelift::codegen::ir::condcodes::{FloatCC, IntCC};
impl Token {
    pub fn is_zero(&self) -> bool {
        match *self {
            Token::Int(i) => i == 0,
            Token::UnsignedInt(u) => u == 0,
            Token::Char(c) => c == 0,
            _ => false,
        }
    }
    pub fn to_int_compare(&self, signed: bool) -> Result<IntCC, ()> {
        match (self, signed) {
            (Token::Less, true) => Ok(IntCC::SignedLessThan),
            (Token::Less, false) => Ok(IntCC::UnsignedLessThan),
            (Token::LessEqual, true) => Ok(IntCC::SignedLessThanOrEqual),
            (Token::LessEqual, false) => Ok(IntCC::UnsignedLessThanOrEqual),
            (Token::Greater, true) => Ok(IntCC::SignedGreaterThan),
            (Token::Greater, false) => Ok(IntCC::UnsignedGreaterThan),
            (Token::GreaterEqual, true) => Ok(IntCC::SignedGreaterThanOrEqual),
            (Token::GreaterEqual, false) => Ok(IntCC::UnsignedGreaterThanOrEqual),
            (Token::EqualEqual, _) => Ok(IntCC::Equal),
            (Token::NotEqual, _) => Ok(IntCC::NotEqual),
            _ => Err(()),
        }
    }
    pub fn to_float_compare(&self) -> Result<FloatCC, ()> {
        match self {
            Token::Less => Ok(FloatCC::LessThan),
            Token::LessEqual => Ok(FloatCC::LessThanOrEqual),
            Token::Greater => Ok(FloatCC::GreaterThan),
            Token::GreaterEqual => Ok(FloatCC::GreaterThanOrEqual),
            Token::EqualEqual => Ok(FloatCC::Equal),
            Token::NotEqual => Ok(FloatCC::NotEqual),
            _ => Err(()),
        }
    }
    pub fn without_assignment(&self) -> Result<Token, ()> {
        Ok(match self {
            Token::PlusEqual => Token::Plus,
            Token::MinusEqual => Token::Minus,
            Token::StarEqual => Token::Star,
            Token::DivideEqual => Token::Divide,
            Token::ModEqual => Token::Mod,
            Token::AndEqual => Token::Ampersand,
            Token::OrEqual => Token::BitwiseOr,
            Token::LeftEqual => Token::ShiftLeft,
            Token::RightEqual => Token::ShiftRight,
            Token::XorEqual => Token::Xor,
            _ => return Err(()),
        })
    }
}

impl Default for Location {
    fn default() -> Self {
        Self {
            line: 1,
            column: 1,
            file: Default::default(),
        }
    }
}

impl std::fmt::Display for Keyword {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        match self {
            Keyword::Alignas
            | Keyword::Alignof
            | Keyword::Bool
            | Keyword::Complex
            | Keyword::Imaginary
            | Keyword::Atomic
            | Keyword::ThreadLocal
            | Keyword::NoReturn
            | Keyword::Generic
            | Keyword::StaticAssert => write!(f, "_{:?}", self),
            Keyword::VaList => write!(f, "va_list"),
            _ => write!(f, "{}", &format!("{:?}", self).to_lowercase()),
        }
    }
}

impl std::fmt::Display for Token {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
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
            BitwiseOr => write!(f, "|"),
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
            UnsignedInt(u) => write!(f, "{}", u),
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
