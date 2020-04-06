use super::{Lexeme, Parser, SyntaxResult};
use crate::data::*;
use crate::data::{
    ast::{CompoundStatement, Declaration, Expr, ExternalDeclaration, Stmt, StmtType},
    lex::Keyword,
    StorageClass,
};
use std::iter::Iterator;

type StmtResult = SyntaxResult<Stmt>;

impl<I: Iterator<Item = Lexeme>> Parser<I> {
    pub fn compound_statement(&mut self) -> SyntaxResult<Locatable<CompoundStatement>> {
        let mut location = self
            .expect(Token::LeftBrace)
            .expect("compound_statement should be called with '{' as the next token")
            .location;
        let mut stmts = vec![];
        let mut pending_errs = vec![];
        while self.peek_token() != Some(&Token::RightBrace) {
            match self.statement() {
                Ok(stmt) => {
                    location = location.merge(stmt.location);
                    stmts.push(stmt);
                }
                Err(err) => {
                    self.panic();
                    pending_errs.push(err);
                    // prevent infinite loops if there's a syntax error at EOF
                    if self.peek_token().is_none() {
                        break;
                    }
                }
            }
        }
        if self.expect(Token::RightBrace).is_err() {
            assert!(self.peek_token().is_none()); // from the 'break' above
            let actual_err = self
                .last_location
                .with(SyntaxError::from("unclosed '{' delimeter at end of file"));
            pending_errs.push(actual_err);
        }
        if let Some(err) = pending_errs.pop() {
            self.error_handler.extend(pending_errs.into_iter());
            Err(err)
        } else {
            Ok(Locatable::new(stmts, location))
        }
    }
    fn declaration(&mut self) -> SyntaxResult<Stmt> {
        let decl = self.external_declaration()?;
        match decl.data.into_declaration() {
            Err(err) => Err(decl.location.with(err)),
            Ok(declaration) => Ok(Stmt::new(StmtType::Decl(declaration), decl.location)),
        }
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
    pub fn statement(&mut self) -> SyntaxResult<Stmt> {
        match self.peek_token() {
            Some(Token::LeftBrace) => Ok(self.compound_statement()?.map(StmtType::Compound)),
            Some(Token::Keyword(k)) => match k {
                // labeled_statement (excluding labels)
                Keyword::Case => {
                    let kw = self.next_token().unwrap();
                    let expr = self.expr()?;
                    self.expect(Token::Colon)?;
                    let inner = Box::new(self.statement()?);
                    Ok(Stmt {
                        location: kw.location.merge(expr.location),
                        data: StmtType::Case(Box::new(expr), inner),
                    })
                }
                Keyword::Default => {
                    let kw = self.next_token().unwrap();
                    self.expect(Token::Colon)?;
                    let inner = self.statement()?;
                    Ok(Stmt {
                        data: StmtType::Default(Box::new(inner)),
                        location: kw.location,
                    })
                }

                // selection_statement
                Keyword::If => self.if_statement(),
                Keyword::Switch => self.switch_statement(),

                // iteration_statement
                Keyword::While => self.while_statement(),
                Keyword::Do => self.do_while_statement(),
                Keyword::For => self.for_statement(),

                // jump_statement
                Keyword::Goto => self.goto_statement(),
                Keyword::Continue => {
                    let kw = self.next_token().unwrap();
                    self.expect(Token::Semicolon)?;
                    Ok(Stmt {
                        data: StmtType::Continue,
                        location: kw.location,
                    })
                }
                Keyword::Break => {
                    let kw = self.next_token().unwrap();
                    self.expect(Token::Semicolon)?;
                    Ok(Stmt {
                        data: StmtType::Break,
                        location: kw.location,
                    })
                }
                Keyword::Return => self.return_statement(),

                // start of an expression statement
                Keyword::Sizeof
                | Keyword::StaticAssert
                | Keyword::Alignas
                | Keyword::Alignof
                | Keyword::Generic => self.expression_statement(),
                decl if decl.is_decl_specifier() => self.declaration(),
                other => {
                    let err = SyntaxError::NotAStatement(*other);
                    Err(self.next_location().with(err))
                }
            },
            Some(Token::Semicolon) => {
                let Locatable { location, .. } = self.next_token().expect("peek is broken");
                Ok(Stmt {
                    data: Default::default(),
                    location,
                })
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
                    return Ok(Stmt {
                        data: StmtType::Label(id.data, Box::new(self.statement()?)),
                        location: id.location,
                    });
                }
                let is_typedef = self.typedefs.get(&id.data).is_some();
                self.unput(Some(Locatable {
                    data: Token::Id(id.data),
                    location: id.location,
                }));
                if is_typedef {
                    self.declaration()
                } else {
                    self.expression_statement()
                }
            }
            _ => self.expression_statement(),
        }
    }
    // expr ;
    fn expression_statement(&mut self) -> SyntaxResult<Stmt> {
        let expr = self.expr()?;
        let end = self.expect(Token::Semicolon)?;
        Ok(Stmt {
            location: expr.location.merge(end.location),
            data: StmtType::Expr(expr),
        })
    }
    // return (expr)? ;
    fn return_statement(&mut self) -> StmtResult {
        let ret_token = self.expect(Token::Keyword(Keyword::Return)).unwrap();
        let expr = self.expr_opt(Token::Semicolon)?;
        Ok(Stmt {
            location: ret_token
                .location
                .maybe_merge(expr.as_ref().map(|l| l.location)),
            data: StmtType::Return(expr),
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
        let condition = self.expr()?;
        self.expect(Token::RightParen)?;
        let body = self.statement()?;
        let otherwise = if self.match_next(&Token::Keyword(Keyword::Else)).is_some() {
            // NOTE: `if (1) ; else ;` is legal!
            Some(Box::new(self.statement()?))
        } else {
            None
        };
        let stmt = StmtType::If(condition, Box::new(body), otherwise);
        Ok(Stmt {
            data: stmt,
            location: start.location,
        })
    }
    /// switch_statement: SWITCH '(' expr ')' statement
    fn switch_statement(&mut self) -> StmtResult {
        let start = self.expect(Token::Keyword(Keyword::Switch))?;
        self.expect(Token::LeftParen)?;
        let expr = self.expr()?;
        self.expect(Token::RightParen)?;
        let body = self.statement()?;
        let stmt = StmtType::Switch(expr, Box::new(body));
        Ok(Stmt {
            data: stmt,
            location: start.location,
        })
    }
    /// while_statement: WHILE '(' expr ')' statement
    fn while_statement(&mut self) -> StmtResult {
        let start = self.expect(Token::Keyword(Keyword::While))?;
        self.expect(Token::LeftParen)?;
        let condition = self.expr()?;
        self.expect(Token::RightParen)?;
        let body = self.statement()?;
        Ok(Stmt {
            data: StmtType::While(condition, Box::new(body)),
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
        let condition = self.expr()?;
        self.expect(Token::RightParen)?;
        self.expect(Token::Semicolon)?;
        let stmt = StmtType::Do(Box::new(body), condition);
        Ok(Stmt {
            data: stmt,
            location: start.location,
        })
    }

    /// expr_opt: expr ';' | ';'
    ///
    /// `token` is the delimiter that ends the expression;
    /// `token` is usually `;` but sometimes `)` (in `for` loops)
    pub(super) fn expr_opt(&mut self, token: Token) -> SyntaxResult<Option<Expr>> {
        if self.match_next(&token).is_some() {
            Ok(None)
        } else {
            let expr = self.expr()?;
            self.expect(token)?;
            Ok(Some(expr))
        }
    }

    /// for_statement:
    ///     FOR '(' expr_opt ';' expr_opt ';' expr_opt ') statement
    ///   | FOR '(' declaration expr_opt ';' expr_opt ') statement
    fn for_statement(&mut self) -> StmtResult {
        let start = self.expect(Token::Keyword(Keyword::For))?;
        let paren = self.expect(Token::LeftParen)?;
        let expr_opt = |this: &mut Self| {
            let expr = this.expr_opt(Token::Semicolon)?;
            let semicolon = this.last_location;
            Ok(if let Some(expr) = expr {
                let location = expr.location.merge(semicolon);
                Stmt::new(StmtType::Expr(expr), location)
            } else {
                Stmt::new(StmtType::default(), semicolon)
            })
        };
        let decl_stmt = match self.peek_token() {
            Some(Token::Keyword(k)) if k.is_decl_specifier() => self.declaration()?,
            Some(Token::Id(id)) => {
                let id = *id;
                if self.typedefs.get(&id).is_some() {
                    self.declaration()?
                } else {
                    expr_opt(self)?
                }
            }
            Some(_) => expr_opt(self)?,
            None => {
                return Err(self
                    .last_location
                    .with(SyntaxError::EndOfFile("expression or ';'")));
            }
        };
        let initializer = Box::new(Stmt {
            data: decl_stmt.data,
            location: paren.location.merge(decl_stmt.location),
        });
        let controlling_expr = self.expr_opt(Token::Semicolon)?;
        let iter_expr = self.expr_opt(Token::RightParen)?;
        let body = Box::new(self.statement()?);
        Ok(Stmt {
            data: StmtType::For {
                initializer,
                condition: controlling_expr.map(Box::new),
                post_loop: iter_expr.map(Box::new),
                body,
            },
            location: start.location,
        })
    }
    /// goto_statement: GOTO identifier ';'
    fn goto_statement(&mut self) -> StmtResult {
        let start = self.expect(Token::Keyword(Keyword::Goto)).unwrap();
        let id = self.expect_id()?;
        self.expect(Token::Semicolon)?;
        Ok(Stmt {
            data: StmtType::Goto(id.data),
            location: start.location.merge(id.location),
        })
    }
}

impl ExternalDeclaration {
    /// If this is a `Declaration`, return all declarations seen.
    /// Otherwise, return the declarator for the function definition.
    fn into_declaration(self) -> Result<Declaration, SyntaxError> {
        match self {
            ExternalDeclaration::Function(def) => Err(SyntaxError::FunctionNotAllowed(def)),
            ExternalDeclaration::Declaration(decl) => Ok(decl),
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::data::ast::*;
    use crate::data::*;
    use crate::test::*;

    fn stmt(stmt: &str) -> CompileResult<Stmt> {
        let mut p = parser(stmt);
        let exp = p.statement();
        if let Some(err) = p.error_handler.pop_front() {
            Err(err)
        } else {
            exp.map_err(CompileError::from)
        }
    }

    fn assert_stmt_display(left: &str, right: &str) {
        assert_eq!(stmt(left).unwrap().data.to_string(), right);
    }
    fn assert_no_change(s: &str) {
        assert_eq!(stmt(s).unwrap().data.to_string(), s);
    }

    #[test]
    // NOTE: this seems to be one of the few tests that checks that the location
    // is correct. If it starts failing, maybe look at the lexer first
    fn test_expr_stmt() {
        let parsed = stmt("1;");
        let expected = Ok(Stmt {
            data: StmtType::Expr(parser("1").expr().unwrap()),
            location: Location {
                file: Location::default().file,
                span: (0..2).into(),
            },
        });
        assert_eq!(parsed, expected);
        assert_eq!(parsed.unwrap().location, expected.unwrap().location);
    }
    #[test]
    fn test_goto() {
        assert_no_change("goto a;");
    }
    #[test]
    fn test_do_while() {
        assert_no_change("do break; while (1);");
    }
    #[test]
    fn test_if() {
        assert_no_change("if (1) break; else continue;");
    }
    #[test]
    fn test_while() {
        assert_stmt_display("while(1);", "while (1) {\n}");
        assert_no_change("while (1) {\n}");
        assert_stmt_display("while (1) { int i = 1; }", "while (1) {\n    int i = 1;\n}");
        assert_no_change("while (1) break;");
    }
    #[test]
    fn test_for() {
        assert_stmt_display(
            "for (int i = 0; i < 10; ++i);",
            "for (int i = 0; (i) < (10); ++(i)) {\n}",
        );
        assert_stmt_display(
            "for (int i = 0, j = 5; ;);",
            "for (int i = 0, j = 5; ;) {\n}",
        );
        assert_stmt_display("for (;;);", "for (;;) {\n}");
        assert_no_change("for (;;) {\n}");
    }
    #[test]
    fn test_switch() {
        assert_stmt_display(
            "switch(1) { default: ; }",
            "switch (1) {
    default:
        {
        }
}",
        );
        assert_stmt_display(
            "switch(1) {
    case 5: case 6: case 7: ;
}",
            "switch (1) {
    case 5:
        case 6:
            case 7:
                {
                }
}",
        );
    }
}
