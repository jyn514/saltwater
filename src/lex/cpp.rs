use super::{Lexer, Token};

impl Lexer<'_> {
    pub(super) fn cpp(&mut self) -> Token {
        unimplemented!("preprocessing");
    }
}
