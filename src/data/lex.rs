use std::borrow::Borrow;
use std::cmp::Ordering;

#[cfg(test)]
use proptest_derive::Arbitrary;

use crate::data::hir::BinaryOp;
use crate::intern::InternedStr;

// holds where a piece of code came from
// should almost always be immutable
#[derive(Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct Span {
    pub start: u32,
    pub end: u32,
}

#[derive(Copy, Clone, Debug, PartialEq)]
pub struct Location {
    pub span: Span,
    pub file: codespan::FileId,
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
pub struct Locatable<T> {
    pub data: T,
    pub location: Location,
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
#[cfg_attr(test, derive(Arbitrary))]
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

    // user-defined types
    Union,
    Struct,
    Enum,
    // the `i` in `typedef int i;`
    UserTypedef(InternedStr),

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

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
#[cfg_attr(test, derive(Arbitrary))]
pub enum AssignmentToken {
    Equal,
    AddEqual,
    SubEqual,
    MulEqual,
    DivEqual,
    ModEqual,
    ShlEqual, // <<=
    ShrEqual, // >>=
    AndEqual,
    OrEqual,
    XorEqual, // ^=
}

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
#[cfg_attr(test, derive(Arbitrary))]
pub enum ComparisonToken {
    Less,
    Greater,
    EqualEqual,
    NotEqual,
    LessEqual,
    GreaterEqual,
}

#[derive(Clone, Debug, PartialEq)]
#[cfg_attr(test, derive(Arbitrary))]
pub enum Literal {
    // literals
    Int(i64),
    UnsignedInt(u64),
    Float(f64),
    Str(Vec<u8>),
    Char(u8),
}

#[derive(Clone, Debug, PartialEq)]
#[cfg_attr(test, derive(Arbitrary))]
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
impl PartialOrd for Location {
    /// NOTE: this only compares the start of the spans, it ignores the end
    fn partial_cmp(&self, other: &Location) -> Option<Ordering> {
        Some(self.span.cmp(&other.span))
    }
}

impl Location {
    pub fn merge<O: Borrow<Self>>(&self, other: O) -> Self {
        use std::cmp::{max, min};

        let other = other.borrow();
        Location {
            span: Span {
                start: min(self.span.start, other.span.start),
                end: max(self.span.end, other.span.end),
            },
            // TODO: what should happen if these come from different files?
            file: self.file,
        }
    }
    /// WARNING: the location for `original` will be on the _left_, not on the right
    pub fn maybe_merge<O: Borrow<Self>>(&self, original: Option<O>) -> Self {
        original.map_or(*self, |l| l.borrow().merge(self))
    }

    pub fn with<T>(self, data: T) -> Locatable<T> {
        Locatable {
            data,
            location: self,
        }
    }

    pub fn error<E: Into<super::error::Error>>(self, error: E) -> super::CompileError {
        self.with(error.into())
    }
}

impl<T: PartialEq> PartialEq for Locatable<T> {
    fn eq(&self, other: &Self) -> bool {
        self.data == other.data
    }
}

impl<T: Eq> Eq for Locatable<T> {}

impl<T> Locatable<T> {
    pub fn new(data: T, location: Location) -> Locatable<T> {
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

impl AssignmentToken {
    pub fn without_assignment(self) -> BinaryOp {
        use AssignmentToken::*;
        use BinaryOp::*;
        match self {
            Equal => panic!("can't call without_assignment on Equal"),
            AddEqual => Add,
            SubEqual => Sub,
            MulEqual => Mul,
            DivEqual => Div,
            ModEqual => Mod,
            AndEqual => BitwiseAnd,
            OrEqual => BitwiseOr,
            ShlEqual => Shl,
            ShrEqual => Shr,
            XorEqual => Xor,
        }
    }
}

#[cfg(test)]
impl Default for Location {
    fn default() -> Self {
        let mut files = crate::Files::default();
        let id = files.add("<test suite>", String::new().into());
        Self {
            span: (0..1).into(),
            file: id,
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

#[cfg(test)]
pub(crate) mod test {
    use crate::*;

    /// Create a new preprocessor with `s` as the input
    pub(crate) fn cpp(s: &str) -> PreProcessor {
        let newline = format!("{}\n", s).into_boxed_str();
        cpp_no_newline(Box::leak(newline))
    }
    /// Create a new preprocessor with `s` as the input, but without a trailing newline
    pub(crate) fn cpp_no_newline(s: &str) -> PreProcessor {
        use target_lexicon::HOST;

        let mut files: Files = Default::default();
        let id = files.add("<test suite>", String::new().into());
        PreProcessor::new(id, s, false, vec![], Box::leak(Box::new(files)), &HOST)
    }

    #[test]
    fn assignment_display() {
        let tokens = [
            "=", "+=", "-=", "*=", "/=", "%=", "&=", "|=", ">>=", "<<=", "^=",
        ];
        for token in &tokens {
            let mut lexer = cpp(token);
            let first = lexer.next().unwrap().unwrap().data;
            assert_eq!(&first.to_string(), *token);
        }
    }
}
