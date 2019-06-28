use super::{Lexeme, Parser};
use crate::data::{Locatable, Stmt, Token};
use std::iter::Iterator;

impl<I: Iterator<Item = Lexeme>> Parser<I> {
    pub fn compound_statement(&mut self) -> Result<Vec<Stmt>, Locatable<String>> {
        if self.expect(Token::LeftBrace).is_none() {
            panic!("compound_statement should be called with '{' as the next token");
        }
        let mut stmts = vec![];
        while self.peek_token() != Some(&Token::RightBrace) {
            stmts.push(self.statement()?);
        }
        if self.expect(Token::RightBrace).is_none() {
            panic!("peek should always be the same as next");
        }
        return Ok(stmts);
    }
    pub fn statement(&mut self) -> Result<Stmt, Locatable<String>> {
        unimplemented!();
    }
}
