use super::{Lexeme, Parser};
use crate::data::{Keyword, Locatable, Stmt, Token};
use std::iter::Iterator;

type StmtResult = Result<Stmt, Locatable<String>>;

impl<I: Iterator<Item = Lexeme>> Parser<I> {
    pub fn compound_statement(&mut self) -> Result<Stmt, Locatable<String>> {
        if self.expect(Token::LeftBrace).is_none() {
            panic!("compound_statement should be called with '{' as the next token");
        }
        let mut stmts = vec![];
        while self.peek_token() != Some(&Token::RightBrace) {
            if let Some(x) = self.statement() {
                stmts.push(x?);
            }
        }
        if self.expect(Token::RightBrace).is_none() {
            panic!("peek should always be the same as next");
        }
        Ok(Stmt::Compound(stmts))
    }
    /// statement
    /// : labeled_statement
    /// | compound_statement
    /// | expression_statement
    /// | selection_statement
    /// | iteration_statement
    /// | jump_statement
    /// ;
    ///
    /// labeled_statement:
    ///     identifier ':' statement
    ///   | CASE constant_expr ':' statement
    ///   | DEFAULT ':' statement
    ///
    pub fn statement(&mut self) -> Option<StmtResult> {
        match self.peek_token() {
            Some(Token::LeftBrace) => Some(self.compound_statement()),
            Some(Token::Keyword(k)) => match k {
                // labeled_statement (excluding labels)
                Keyword::Case => unimplemented!(),
                Keyword::Default => unimplemented!(),

                // selection_statement
                Keyword::If => Some(self.if_statement()),
                Keyword::Switch => Some(self.switch_statement()),

                // iteration_statement
                Keyword::While => Some(self.while_statement()),
                Keyword::Do => Some(self.do_while_statement()),
                Keyword::For => Some(self.for_statement()),

                // jump_statement
                Keyword::Goto => Some(self.goto_statement()),
                Keyword::Continue => unimplemented!(),
                Keyword::Break => unimplemented!(),
                Keyword::Return => unimplemented!(),
                x => {
                    if !x.is_decl_specifier() {
                        panic!("unrecognized keyword '{}' while parsing statement", x);
                    }
                    Some(Err(Locatable {
                        data: format!("expected statement, got '{}'. help: {} is a declaration specifier, but a declaration was not expected here.", x, x),
                        location: self.next_location().clone(),
                    }))
                }
            },
            Some(Token::Id(_)) => {
                let locatable = self.next_token().unwrap();
                if self.match_next(&Token::Colon).is_some() {
                    match locatable.data {
                        Token::Id(id) => Some(Ok(Stmt::Label(
                            id,
                            match self.statement() {
                                Some(Ok(x)) => Some(Box::new(x)),
                                Some(Err(err)) => return Some(Err(err)),
                                None => None,
                            },
                        ))),
                        _ => panic!("peek should always be the same as next"),
                    }
                } else {
                    self.unput(Some(locatable));
                    Some(self.expr().map(Stmt::Expr))
                }
            }
            _ => {
                if self.match_next(&Token::Semicolon).is_some() {
                    None
                } else {
                    let expr = self.expr();
                    self.expect(Token::Semicolon);
                    Some(expr.map(Stmt::Expr))
                }
            }
        }
    }
    /// if_statement:
    ///     IF '(' expr ')' statement
    ///   | IF '(' expr ')' statement ELSE statement
    fn if_statement(&mut self) -> StmtResult {
        let start = self.expect(Token::Keyword(Keyword::If));
        self.expect(Token::LeftParen);
        let condition = self.expr()?;
        self.expect(Token::RightParen);
        let body = self.statement();
        let otherwise = if self.match_next(&Token::Keyword(Keyword::Else)).is_some() {
            // NOTE: `if (1) ; else ;` is legal!
            self.statement()
        } else {
            None
        };
        unimplemented!();
    }
    /// switch_statement: SWITCH '(' expr ')' statement
    fn switch_statement(&mut self) -> StmtResult {
        let start = self.expect(Token::Keyword(Keyword::Switch));
        self.expect(Token::LeftParen);
        let expr = self.expr();
        self.expect(Token::RightParen);
        let body = self.statement();
        unimplemented!();
    }
    /// while_statement: WHILE '(' expr ')' statement
    fn while_statement(&mut self) -> StmtResult {
        let start = self.expect(Token::Keyword(Keyword::While));
        self.expect(Token::LeftParen);
        let expr = self.expr()?.truthy()?;
        self.expect(Token::RightParen);
        let body = self.statement();
        unimplemented!();
    }
    /// do_while_statement: DO statement WHILE '(' expr ')' ';'
    fn do_while_statement(&mut self) -> StmtResult {
        let start = self.expect(Token::Keyword(Keyword::Do));
        let body = self.statement();
        self.expect(Token::Keyword(Keyword::While));
        self.expect(Token::LeftParen);
        let expr = self.expr()?.truthy();
        self.expect(Token::RightParen);
        self.expect(Token::Semicolon);
        unimplemented!();
    }
    /// for_statement:
    ///     FOR '(' expr_opt ';' expr_opt ';' expr_opt ') statement
    ///   | FOR '(' declaration expr_opt ';' expr_opt ') statement
    fn for_statement(&mut self) -> StmtResult {
        let start = self.expect(Token::Keyword(Keyword::For));
        self.expect(Token::LeftParen);
        match self.peek_token() {
            Some(Token::Keyword(k)) if k.is_decl_specifier() => {
                let decl = self.declaration();
            }
            Some(_) => {
                let init = self.expr_opt(Token::Semicolon);
            }
            None => {
                return Err(Locatable {
                    location: self.last_location.as_ref().unwrap().clone(),
                    data: "expected expression or ';', got <end-of-file>".to_string(),
                })
            }
        };
        let controlling_expr = self.expr_opt(Token::Semicolon);
        let iter_expr = self.expr_opt(Token::RightParen);
        let body = self.statement();
        unimplemented!();
    }
    /// goto_statement: GOTO identifier ';'
    fn goto_statement(&mut self) -> StmtResult {
        let start = self.expect(Token::Keyword(Keyword::Goto));
        let id = self.expect(Token::Id(String::new()));
        self.expect(Token::Semicolon);
        unimplemented!();
    }
}
