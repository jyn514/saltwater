#[derive(Clone, Copy, Debug)]
pub enum Keyword {
    // keywords
    IF,
    ELSE,
    DO,
    WHILE,
    FOR,
    SWITCH,
    CASE,
    DEFAULT,
    BREAK,
    CONTINUE,
    RETURN,
    GOTO,

    // types
    BOOL,
    CHAR,
    SHORT,
    INT,
    LONG,
    FLOAT,
    DOUBLE,
    VOID,
    SIGNED,
    UNSIGNED,
    TYPEDEF,
    UNION,
    STRUCT,

    // qualifiers
    CONST,
    VOLATILE,

    // storage classes
    AUTO,
    REGISTER,
    STATIC,
    EXTERN,

    SIZEOF
}

#[derive(Debug)]
pub enum Token {
    PlusPlus,
    PlusEqual,
    MinusMinus,
    MinusEqual,
    EqualEqual,

    Plus,
    Minus,
    Star,
    Divide,
    Equal,

    // literals
    Int(i64),
    Str(String),
    Char(char),
    Id(String),

    Keyword(Keyword)
}

// holds where a piece of code came from
// should almost always be immutable
#[derive(Clone, Debug)]
pub struct Location<'a> {
    // if there's a 4 GB input file, we have bigger problems
    pub line: u32,
    pub column: u32,
    pub file: &'a str
}

#[derive(Debug)]
pub struct Locatable<'a, T> {
    pub data: T,
    pub location: Location<'a>
}
