use super::{Lexeme, Parser};
use crate::data::{Locatable, Stmt};
use std::iter::Iterator;

impl<I: Iterator<Item = Lexeme>> Parser<I> {
    pub fn compound_statement(&mut self) -> Result<Vec<Stmt>, Locatable<String>> {
        unimplemented!()
    }
}
