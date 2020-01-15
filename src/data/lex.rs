use crate::intern::InternedStr;
use std::cmp::Ordering;
use std::fmt;
use std::ops::{Range, RangeInclusive};

// holds where a piece of code came from
// should almost always be immutable
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub struct Location {
    pub span: Span,
    pub filename: InternedStr,
}

#[derive(Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct Span {
    pub offset: u32,
    pub length: u32,
}

// because { 0, 5 } means 5 numbers starting at 0: [0, 1, 2, 3, 4] == 0..5
impl From<Span> for Range<u32> {
    fn from(span: Span) -> Self {
        span.offset..(span.offset + span.length)
    }
}

impl From<Span> for RangeInclusive<u32> {
    #[allow(clippy::range_minus_one)]
    fn from(span: Span) -> Self {
        span.offset..=(span.offset + span.length - 1)
    }
}

impl From<Range<u32>> for Span {
    /// panics if range.end <= range.start
    fn from(range: Range<u32>) -> Self {
        Span {
            offset: range.start,
            length: range.end - range.start,
        }
    }
}

impl From<RangeInclusive<u32>> for Span {
    /// panics if range.end < range.start
    fn from(range: RangeInclusive<u32>) -> Self {
        Span {
            offset: *range.start(),
            length: range.end() - range.start() + 1,
        }
    }
}

impl fmt::Display for Span {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let r: Range<_> = (*self).into();
        write!(f, "{:?}", r)
    }
}

impl Span {
    pub(crate) fn merge(self, other: Self) -> Self {
        use std::cmp::min;
        let (left, right): (Range<_>, Range<_>) = (self.into(), other.into());
        let min_start = min(left.start, right.start);
        let (first, last) = if left.end < right.end {
            // left ends first
            (left, right)
        } else {
            (right, left)
        };
        if first.end < last.start {
            panic!("ranges must overlap if you want to merge them");
        }
        (min_start..last.end).into()
    }
}

impl Location {
    pub(crate) fn merge(self, other: &Self) -> Self {
        Self {
            span: self.span.merge(other.span),
            ..self
        }
    }
    /*
    /// Calculate a ((start_line, start_column), (end_line, end_column)) tuple
    /// from the offset.
    // TODO: cache some of this so we don't recalculate every time
    // u32: if there's a 4 GB input file, we have bigger problems
    pub fn calculate_line_column(self, file: &str) -> ((u32, u32), (u32, u32)) {
        let end = self.span.offset + self.span.length - 1;
        // avoid panic if file is empty
        if end == 0 {
            return ((1, 1), (1, 1));
        }

        let (mut line, mut column) = (1, 1);
        let mut start = None;
        for (i, c) in file.chars().enumerate() {
            if let Some(start) = start {
                if end == i {
                    return (start, (line, column));
                }
            } else if self.span.offset == i {
                if end == i {
                    return ((line, column), (line, column));
                }
                start = Some((line, column));
            }
            if c == '\n' {
                line += 1;
                column = 1;
            } else {
                column += 1;
            }
        }
        // avoid panic at end of file
        if self.span.offset == file.len() && end == file.len() {
            return ((line, column), (line, column));
        }
        unreachable!(
            "passed a span not in the file (len: {}): {}",
            file.len(),
            self.span
        );
    }
    */
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
    Str(InternedStr),
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
}

/* impls */
impl PartialOrd for Location {
    /// NOTE: this only compares the start of the spans, it ignores the end
    fn partial_cmp(&self, other: &Location) -> Option<Ordering> {
        if self.filename == other.filename {
            Some(self.span.cmp(&other.span))
        } else {
            None
        }
    }
}

impl<T: PartialEq> PartialEq for Locatable<T> {
    fn eq(&self, other: &Self) -> bool {
        self.data == other.data
    }
}

impl<T: Eq> Eq for Locatable<T> {}
impl<T> Locatable<T> {
    pub const fn new(data: T, location: Location) -> Self {
        Self { data, location }
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

impl Default for Location {
    fn default() -> Self {
        Self {
            span: (0..1).into(),
            filename: Default::default(),
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
            Str(s) => write!(f, "\"{}\"", s),
            Char(c) => write!(f, "{}", c),
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
        write!(f, "{}=", self.without_assignment())
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
mod test {
    use super::{Location, Span};
    use crate::intern::InternedStr;
    #[test]
    fn span_to_from_range() {
        let span = Span {
            offset: 0,
            length: 5,
        };
        assert_eq!(0..5, span.into());
        assert_eq!(0..=4, span.into());
        assert_eq!(span, (0..5).into());
        assert_eq!(span, (0..=4).into());
    }
}
