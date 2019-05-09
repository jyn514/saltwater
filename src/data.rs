#[derive(Debug)]
pub enum TokenType {
    Plus,
    Minus,
    Star,
    Divide,
    Int(i64)
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

pub type Token<'a> = Locatable<'a, TokenType>;
pub type Error<'a> = Locatable<'a, String>;
