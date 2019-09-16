use super::{Lexeme, Parser};
use crate::data::prelude::*;
use crate::data::{Keyword, StorageClass};
use crate::utils::warn;
use std::iter::Iterator;

type StmtResult = Result<Stmt, Locatable<String>>;

impl<I: Iterator<Item = Lexeme>> Parser<I> {
    pub fn compound_statement(&mut self) -> Result<Option<Stmt>, Locatable<String>> {
        let start = self
            .expect(Token::LeftBrace)
            .expect("compound_statement should be called with '{' as the next token");
        let mut stmts = vec![];
        // TODO: this behaves very badly for `int i, j;` because it doesn't look at self.pending
        // TODO: refactor Stmt::Decl to have a list of declarations
        while self.peek_token() != Some(&Token::RightBrace) {
            if let Some(x) = self.statement()? {
                stmts.push(x);
            }
        }
        if self.expect(Token::RightBrace).is_err() {
            panic!("peek should always be the same as next");
        }
        Ok(if stmts.is_empty() {
            None
        } else {
            Some(Stmt {
                data: StmtType::Compound(stmts),
                location: start.location,
            })
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
    /// Result: whether there was an error in the program source
    /// Option: empty semicolons still count as a statement (so case labels can work)
    pub fn statement(&mut self) -> Result<Option<Stmt>, Locatable<String>> {
        match self.peek_token() {
            Some(Token::LeftBrace) => {
                self.enter_scope();
                let stmts = self.compound_statement();
                self.leave_scope();
                stmts
            }
            Some(Token::Keyword(k)) => match k {
                // labeled_statement (excluding labels)
                Keyword::Case => unimplemented!("case"),
                Keyword::Default => unimplemented!("default"),

                // selection_statement
                Keyword::If => Ok(Some(self.if_statement()?)),
                Keyword::Switch => Ok(Some(self.switch_statement()?)),

                // iteration_statement
                Keyword::While => Ok(Some(self.while_statement()?)),
                Keyword::Do => Ok(Some(self.do_while_statement()?)),
                Keyword::For => Ok(Some(self.for_statement()?)),

                // jump_statement
                Keyword::Goto => Ok(Some(self.goto_statement()?)),
                Keyword::Continue => unimplemented!("continue"),
                Keyword::Break => unimplemented!("break"),
                Keyword::Return => Ok(Some(self.return_statement()?)),

                // start of an expression statement
                Keyword::Sizeof => self.expression_statement(),
                decl if decl.is_decl_specifier() => {
                    let decls = self.declaration()?;
                    let location = match decls.front() {
                        Some(decl) => decl.location.clone(),
                        None => return Ok(None),
                    };
                    Ok(Some(Stmt {
                        data: StmtType::Decl(decls),
                        location,
                    }))
                }
                other => unreachable!("unrecognized keyword '{}' while parsing statement", other),
            },
            Some(Token::Semicolon) => {
                self.next_token();
                Ok(None)
            }
            Some(Token::Id(_)) => {
                let locatable = self.next_token().unwrap();
                let id = match locatable.data {
                    Token::Id(id) => Locatable {
                        data: id,
                        location: locatable.location,
                    },
                    _ => unreachable!("peek should always be the same as next"),
                };
                if self.match_next(&Token::Colon).is_some() {
                    return Ok(Some(Stmt {
                        data: StmtType::Decl(self.declaration()?),
                        location: id.location,
                    }));
                }
                let is_typedef = match self.scope.get(&id.data) {
                    Some(typedef) => typedef.storage_class == StorageClass::Typedef,
                    _ => false,
                };
                self.unput(Some(Locatable {
                    data: Token::Id(id.data),
                    location: id.location,
                }));
                if is_typedef {
                    let decls = self.declaration()?;
                    let location = match decls.front() {
                        Some(decl) => decl.location.clone(),
                        None => return Ok(None),
                    };
                    Ok(Some(Stmt {
                        data: StmtType::Decl(decls),
                        location,
                    }))
                } else {
                    self.expression_statement()
                }
            }
            _ => self.expression_statement(),
        }
    }
    fn expression_statement(&mut self) -> Result<Option<Stmt>, Locatable<String>> {
        let expr = self.expr()?;
        let end = self.expect(Token::Semicolon)?;
        Ok(Some(Stmt {
            data: StmtType::Expr(expr),
            location: end.location,
        }))
    }
    fn return_statement(&mut self) -> StmtResult {
        let ret_token = self.expect(Token::Keyword(Keyword::Return)).unwrap();
        let expr = self.expr_opt(Token::Semicolon)?;
        let current = self
            .current_function
            .as_mut()
            .expect("should have current_function set when parsing statements");
        let ret_type = &current.return_type;
        let stmt = match (expr, *ret_type != Type::Void) {
            (None, false) => StmtType::Return(None),
            (None, true) => {
                return Err(Locatable {
                    data: format!("function '{}' does not return a value", current.id),
                    location: ret_token.location,
                })
            }
            (Some(expr), false) => {
                return Err(Locatable {
                    data: format!("void function '{}' should not return a value", current.id),
                    location: expr.location,
                })
            }
            (Some(expr), true) => {
                let expr = expr.rval();
                if expr.ctype != *ret_type {
                    StmtType::Return(Some(Expr::cast(expr, ret_type)?))
                } else {
                    StmtType::Return(Some(expr))
                }
            }
        };
        Ok(Stmt {
            data: stmt,
            location: ret_token.location,
        })
    }
    /// if_statement:
    ///     IF '(' expr ')' statement
    ///   | IF '(' expr ')' statement ELSE statement
    fn if_statement(&mut self) -> StmtResult {
        let start = self
            .expect(Token::Keyword(Keyword::If))
            .expect("parser shouldn't call if_statement without an if");
        self.expect(Token::LeftParen)?;
        let condition = self.expr()?.rval();
        self.expect(Token::RightParen)?;
        let body = self.statement()?;
        let otherwise = if self.match_next(&Token::Keyword(Keyword::Else)).is_some() {
            // NOTE: `if (1) ; else ;` is legal!
            self.statement()?
        } else {
            None
        };
        let stmt = match (body, otherwise) {
            (None, None) => {
                not_executed_warning(
                    "missing both if body and else body",
                    "if (expr) {}",
                    "expr;",
                    &condition.location,
                );
                StmtType::Expr(condition)
            }
            (None, Some(body)) => {
                let location = condition.location.clone();
                StmtType::If(condition.logical_not(location)?, Box::new(body), None)
            }
            (Some(body), maybe_else) => {
                StmtType::If(condition, Box::new(body), maybe_else.map(Box::new))
            }
        };
        Ok(Stmt {
            data: stmt,
            location: start.location,
        })
    }
    /// switch_statement: SWITCH '(' expr ')' statement
    fn switch_statement(&mut self) -> StmtResult {
        let start = self.expect(Token::Keyword(Keyword::Switch))?;
        self.expect(Token::LeftParen)?;
        let expr = self.expr()?.rval();
        self.expect(Token::RightParen)?;
        let body = self.statement()?;
        let stmt = if let Some(stmt) = body {
            unimplemented!("switch body (esp. labels)");
        } else {
            not_executed_warning(
                "empty switch body is never executed",
                "switch (expr) {}",
                "expr;",
                &expr.location,
            );
            StmtType::Expr(expr)
        };
        Ok(Stmt {
            data: stmt,
            location: start.location,
        })
    }
    /// while_statement: WHILE '(' expr ')' statement
    fn while_statement(&mut self) -> StmtResult {
        let start = self.expect(Token::Keyword(Keyword::While))?;
        self.expect(Token::LeftParen)?;
        let condition = self.expr()?.truthy()?;
        self.expect(Token::RightParen)?;
        let body = self.statement()?;
        Ok(Stmt {
            data: StmtType::While(condition, body.map(Box::new)),
            location: start.location,
        })
    }
    /// do_while_statement: DO statement WHILE '(' expr ')' ';'
    fn do_while_statement(&mut self) -> StmtResult {
        let start = self
            .expect(Token::Keyword(Keyword::Do))
            .unwrap_or_else(|_| {
                panic!("do_while_statement should only be called with `do` as next token")
            });
        let body = self.statement()?;
        self.expect(Token::Keyword(Keyword::While))?;
        self.expect(Token::LeftParen)?;
        let condition = self.expr()?.truthy()?;
        self.expect(Token::RightParen)?;
        self.expect(Token::Semicolon)?;
        let stmt = if let Some(body) = body {
            StmtType::Do(Box::new(body), condition)
        } else {
            not_executed_warning(
                "empty body for do-while statement",
                "do {} while (expr)",
                "while (expr) {}",
                &start.location,
            );
            StmtType::While(condition, None)
        };
        Ok(Stmt {
            data: stmt,
            location: start.location,
        })
    }
    /// for_statement:
    ///     FOR '(' expr_opt ';' expr_opt ';' expr_opt ') statement
    ///   | FOR '(' declaration expr_opt ';' expr_opt ') statement
    fn for_statement(&mut self) -> StmtResult {
        let start = self.expect(Token::Keyword(Keyword::For));
        self.expect(Token::LeftParen)?;
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
        let start = self.expect(Token::Keyword(Keyword::Goto)).unwrap();
        let id = match self.expect(Token::Id(String::new()))?.data {
            Token::Id(id) => id,
            _ => unreachable!("expect should only return an Id if called with Token::Id"),
        };
        self.expect(Token::Semicolon)?;
        Ok(Stmt {
            data: StmtType::Goto(id),
            location: start.location,
        })
    }
}

fn not_executed_warning(description: &str, from: &str, to: &str, location: &Location) {
    warn(&format!("{} will be rewritten internally. help: to silence this warning, rewrite it yourself: `{}` => `{}`", description, from, to), location);
}

#[cfg(test)]
mod tests {
    use super::super::tests::*;
    use crate::data::{Locatable, Location, Stmt, StmtType};
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
        let expected = Ok(Some(Stmt {
            data: StmtType::Expr(parser("1").expr().unwrap()),
            location: Location {
                line: 1,
                column: 1,
                file: "<test-suite>".into(),
            },
        }));
        assert_eq!(dbg!(parsed), dbg!(expected))
    }
}
