#[derive(Clone, Copy, Debug, PartialEq)]
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
    Str(String),
    Char(char),
    Id(String),

    Keyword(Keyword)
}

// holds where a piece of code came from
// should almost always be immutable
#[derive(Clone, Debug, PartialEq)]
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
