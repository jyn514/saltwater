use crate::intern::InternedStr;

//use codespan::{FileId, Span};

use std::borrow::Borrow;
use std::cmp::Ordering;

/*
// holds where a piece of code came from
// should almost always be immutable
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub struct Location {
    pub span: Span,
    pub file: FileId,
}
*/

#[derive(Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct Span {
    start: u32,
    end: u32,
}
pub trait LocationTrait: Copy + std::fmt::Debug + PartialEq + Sized {
    fn merge<O: Borrow<Self>>(&self, other: O) -> Self;

    fn with<T>(self, data: T) -> Locatable<T, Self> {
        Locatable {
            data,
            location: self,
        }
    }

    fn error<E: Into<super::error::Error>>(self, error: E) -> super::CompileError<Self> {
        self.with(error.into())
    }
}
#[derive(Copy, Clone, Debug, PartialEq)]
pub struct DefaultLocation {
    pub span: Span,
    pub file: (),
}

use std::ops::Range;
impl From<Range<u32>> for Span {
    fn from(r: Range<u32>) -> Span {
        Span {
            start: r.start,
            end: r.end,
        }
    }
}

#[derive(Copy, Clone, Debug)]
pub struct Locatable<T, L: LocationTrait = DefaultLocation> {
    pub data: T,
    pub location: L,
}

impl<T> Locatable<T> {
    pub fn map<S, F: FnOnce(T) -> S>(self, f: F) -> Locatable<S> {
        Locatable {
            data: f(self.data),
            location: self.location,
        }
    }
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

#[derive(Copy, Clone, Debug, PartialEq)]
pub enum AssignmentToken {
    Equal,
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
}

#[derive(Copy, Clone, Debug, PartialEq)]
pub enum ComparisonToken {
    Less,
    Greater,
    EqualEqual,
    NotEqual,
    LessEqual,
    GreaterEqual,
}

#[derive(Clone, Debug, PartialEq)]
pub enum Literal {
    // literals
    Int(i64),
    UnsignedInt(u64),
    Float(f64),
    Str(Vec<u8>),
    Char(u8),
}

#[derive(Clone, Debug, PartialEq)]
pub enum Token {
    PlusPlus,
    MinusMinus,
    Assignment(AssignmentToken),
    Comparison(ComparisonToken),

    Plus,
    Minus,
    Star,
    Divide,
    Mod,
    Xor,
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

    Keyword(Keyword),
    Literal(Literal),
    Id(InternedStr),

    // Misc
    Ellipsis,
    StructDeref, // ->
    Hash,        // #, used for preprocessing
}

/* impls */
impl PartialOrd for DefaultLocation {
    /// NOTE: this only compares the start of the spans, it ignores the end
    fn partial_cmp(&self, other: &DefaultLocation) -> Option<Ordering> {
        Some(self.span.cmp(&other.span))
    }
}

impl LocationTrait for DefaultLocation {
    fn merge<O: Borrow<Self>>(&self, other: O) -> Self {
        use std::cmp::{max, min};

        let other = other.borrow();
        DefaultLocation {
            span: Span {
                start: min(self.span.start, other.span.start),
                end: max(self.span.end, other.span.end),
            },
            file: (),
        }
    }
}

impl<T: PartialEq> PartialEq for Locatable<T> {
    fn eq(&self, other: &Self) -> bool {
        self.data == other.data
    }
}

impl<T: Eq> Eq for Locatable<T> {}

impl<T, L: LocationTrait> Locatable<T, L> {
    pub fn new(data: T, location: L) -> Locatable<T, L> {
        location.with(data)
    }
}

impl Token {
    pub const EQUAL: Token = Token::Assignment(AssignmentToken::Equal);
}

impl Literal {
    pub fn is_zero(&self) -> bool {
        match *self {
            Literal::Int(i) => i == 0,
            Literal::UnsignedInt(u) => u == 0,
            Literal::Char(c) => c == 0,
            _ => false,
        }
    }
}

/*
use cranelift::codegen::ir::condcodes::{FloatCC, IntCC};
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
*/
impl AssignmentToken {
    pub fn without_assignment(self) -> Token {
        use AssignmentToken::*;
        match self {
            Equal => Equal.into(), // there's not really a good behavior here...
            PlusEqual => Token::Plus,
            MinusEqual => Token::Minus,
            StarEqual => Token::Star,
            DivideEqual => Token::Divide,
            ModEqual => Token::Mod,
            AndEqual => Token::Ampersand,
            OrEqual => Token::BitwiseOr,
            LeftEqual => Token::ShiftLeft,
            RightEqual => Token::ShiftRight,
            XorEqual => Token::Xor,
        }
    }
}

#[cfg(test)]
impl Default for DefaultLocation {
    fn default() -> Self {
        Self {
            span: (0..1).into(),
            file: (),
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
            | Keyword::Generic => write!(f, "_{:?}", self),
            Keyword::NoReturn => write!(f, "_Noreturn"),
            Keyword::ThreadLocal => write!(f, "_Thread_local"),
            Keyword::StaticAssert => write!(f, "_Static_assert"),
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
            MinusMinus => write!(f, "--"),
            ShiftRight => write!(f, ">>"),
            ShiftLeft => write!(f, "<<"),
            Plus => write!(f, "+"),
            Minus => write!(f, "-"),
            Star => write!(f, "*"),
            Divide => write!(f, "/"),
            Xor => write!(f, "^"),
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

            Assignment(a) => write!(f, "{}", a),
            Comparison(c) => write!(f, "{}", c),
            Literal(lit) => write!(f, "{}", lit),
            Id(id) => write!(f, "{}", id),
            Keyword(k) => write!(f, "{}", k),

            Ellipsis => write!(f, "..."),
            StructDeref => write!(f, "->"),
            Hash => write!(f, "#"),
        }
    }
}

impl std::fmt::Display for Literal {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        use Literal::*;
        match self {
            Int(i) => write!(f, "{}", i),
            UnsignedInt(u) => write!(f, "{}", u),
            Float(n) => write!(f, "{}", n),
            Str(s) => write!(f, "\"{}\"", String::from_utf8_lossy(s)),
            Char(c) => write!(f, "'{}'", char::from(*c).escape_default()),
        }
    }
}

impl std::fmt::Display for ComparisonToken {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        use ComparisonToken::*;
        let s = match self {
            EqualEqual => "==",
            NotEqual => "!=",
            Less => "<",
            LessEqual => "<=",
            Greater => ">",
            GreaterEqual => ">=",
        };
        write!(f, "{}", s)
    }
}

impl std::fmt::Display for AssignmentToken {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        if *self == AssignmentToken::Equal {
            write!(f, "=")
        } else {
            write!(f, "{}=", self.without_assignment())
        }
    }
}

impl From<Literal> for Token {
    fn from(l: Literal) -> Self {
        Token::Literal(l)
    }
}

impl From<AssignmentToken> for Token {
    fn from(a: AssignmentToken) -> Self {
        Token::Assignment(a)
    }
}

impl From<ComparisonToken> for Token {
    fn from(a: ComparisonToken) -> Self {
        Token::Comparison(a)
    }
}
