use super::{Lexeme, Parser};
use crate::data::{Expr, Keyword, Locatable, Location, Stmt, Token};
use crate::utils::warn;
use std::iter::Iterator;

type StmtResult = Result<Stmt, Locatable<String>>;

impl<I: Iterator<Item = Lexeme>> Parser<I> {
    pub fn compound_statement(&mut self) -> Result<Option<Stmt>, Locatable<String>> {
        if self.expect(Token::LeftBrace).is_none() {
            panic!("compound_statement should be called with '{' as the next token");
        }
        let mut stmts = vec![];
        while self.peek_token() != Some(&Token::RightBrace) {
            if let Some(x) = self.statement()? {
                stmts.push(x);
            }
        }
        if self.expect(Token::RightBrace).is_none() {
            panic!("peek should always be the same as next");
        }
        Ok(if stmts.is_empty() {
            None
        } else {
            Some(Stmt::Compound(stmts))
        })
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
    pub fn statement(&mut self) -> Result<Option<Stmt>, Locatable<String>> {
        match self.peek_token() {
            Some(Token::LeftBrace) => self.compound_statement(),
            Some(Token::Keyword(k)) => match k {
                // labeled_statement (excluding labels)
                Keyword::Case => unimplemented!(),
                Keyword::Default => unimplemented!(),

                // selection_statement
                Keyword::If => Ok(Some(self.if_statement()?)),
                Keyword::Switch => Ok(Some(self.switch_statement()?)),

                // iteration_statement
                Keyword::While => Ok(Some(self.while_statement()?)),
                Keyword::Do => Ok(Some(self.do_while_statement()?)),
                Keyword::For => Ok(Some(self.for_statement()?)),

                // jump_statement
                Keyword::Goto => Ok(Some(self.goto_statement()?)),
                Keyword::Continue => unimplemented!(),
                Keyword::Break => unimplemented!(),
                Keyword::Return => {
                    self.next_token();
                    Ok(Some(Stmt::Return(self.expr_opt(Token::Semicolon)?)))
                }
                x => {
                    if !x.is_decl_specifier() {
                        panic!("unrecognized keyword '{}' while parsing statement", x);
                    }
                    Err(Locatable {
                        data: format!("expected statement, got '{}'. help: {} is a declaration specifier, but a declaration was not expected here.", x, x),
                        location: self.next_location().clone(),
                    })
                }
            },
            Some(Token::Id(_)) => {
                let locatable = self.next_token().unwrap();
                if self.match_next(&Token::Colon).is_some() {
                    match locatable.data {
                        Token::Id(id) => Ok(Some(Stmt::Label(id, self.statement()?.map(Box::new)))),
                        _ => panic!("peek should always be the same as next"),
                    }
                } else {
                    self.unput(Some(locatable));
                    Ok(Some(Stmt::Expr(self.expr()?)))
                }
            }
            _ => {
                if self.match_next(&Token::Semicolon).is_some() {
                    Ok(None)
                } else {
                    let expr = self.expr()?;
                    self.expect(Token::Semicolon);
                    Ok(Some(Stmt::Expr(expr)))
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
        let body = self.statement()?;
        let otherwise = if self.match_next(&Token::Keyword(Keyword::Else)).is_some() {
            // NOTE: `if (1) ; else ;` is legal!
            self.statement()?
        } else {
            None
        };
        match (body, otherwise) {
            (None, None) => {
                not_executed_warning(
                    "missing both if body and else body",
                    "if (expr) {}",
                    "expr;",
                    &condition.location,
                );
                Ok(Stmt::Expr(condition))
            }
            (None, Some(body)) => Ok(Stmt::If(condition.logical_not()?, Box::new(body), None)),
            (Some(body), maybe_else) => Ok(Stmt::If(
                condition,
                Box::new(body),
                maybe_else.map(Box::new),
            )),
        }
    }
    /// switch_statement: SWITCH '(' expr ')' statement
    fn switch_statement(&mut self) -> StmtResult {
        let start = self.expect(Token::Keyword(Keyword::Switch));
        self.expect(Token::LeftParen);
        let expr = self.expr()?;
        self.expect(Token::RightParen);
        let body = self.statement()?;
        if let Some(stmt) = body {
            unimplemented!("switch body (esp. labels)");
        } else {
            not_executed_warning(
                "empty switch body is never executed",
                "switch (expr) {}",
                "expr;",
                &expr.location,
            );
            Ok(Stmt::Expr(expr))
        }
    }
    /// while_statement: WHILE '(' expr ')' statement
    fn while_statement(&mut self) -> StmtResult {
        let start = self.expect(Token::Keyword(Keyword::While));
        self.expect(Token::LeftParen);
        let condition = self.expr()?.truthy()?;
        self.expect(Token::RightParen);
        let body = self.statement()?;
        Ok(Stmt::While(condition, body.map(Box::new)))
    }
    /// do_while_statement: DO statement WHILE '(' expr ')' ';'
    fn do_while_statement(&mut self) -> StmtResult {
        let start = self.expect(Token::Keyword(Keyword::Do)).unwrap_or_else(|| {
            panic!("do_while_statement should only be called with `do` as next token")
        });
        let body = self.statement()?;
        self.expect(Token::Keyword(Keyword::While));
        self.expect(Token::LeftParen);
        let condition = self.expr()?.truthy()?;
        self.expect(Token::RightParen);
        self.expect(Token::Semicolon);
        if let Some(body) = body {
            Ok(Stmt::Do(Box::new(body), condition))
        } else {
            not_executed_warning(
                "empty body for do-while statement",
                "do {} while (expr)",
                "while (expr) {}",
                &start.location,
            );
            Ok(Stmt::While(condition, None))
        }
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
        let controlling_expr = self.expr_opt(Token::Semicolon)?.map(Expr::truthy);
        let iter_expr = self.expr_opt(Token::RightParen);
        let body = self.statement();
        unimplemented!("for loops");
    }
    /// goto_statement: GOTO identifier ';'
    fn goto_statement(&mut self) -> StmtResult {
        let start = self.expect(Token::Keyword(Keyword::Goto));
        if let Some(Locatable {
            data: Token::Id(id),
            ..
        }) = self.expect(Token::Id(String::new()))
        {
            self.expect(Token::Semicolon);
            Ok(Stmt::Goto(id))
        } else {
            unimplemented!("handle error in GOTO");
        }
    }
}

fn not_executed_warning(description: &str, from: &str, to: &str, location: &Location) {
    warn(&format!("{} will be rewritten internally. help: to silence this warning, rewrite it yourself: `{}` => `{}`", description, from, to), location);
}

#[cfg(test)]
mod tests {
    use super::super::tests::*;
    use crate::data::{Locatable, Stmt};
    fn parse_stmt(stmt: &str) -> Result<Option<Stmt>, Locatable<String>> {
        parser(stmt).statement()
    }
    #[test]
    // NOTE: this seems to be one of the few tests that checks that the location
    // is correct. If it starts failing, maybe look at the lexer first
    // NOTE: the debug output will be lost in a sea of 'extraneous semicolon' warnings
    // until I fix the error architecture.
    // Try `cargo test -- --nocapture 2>&1 | grep -v semicolon` in the meantime
    fn test_expr_stmt() {
        let parsed = parse_stmt("1;");
        let expected = Ok(Some(Stmt::Expr(parser("1").expr().unwrap())));
        assert!(dbg!(parsed) == dbg!(expected))
    }
}
