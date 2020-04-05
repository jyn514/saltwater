use super::FunctionAnalyzer;
use crate::data::{ast, error::SemanticError, hir::*, lex::Locatable, Location};

impl FunctionAnalyzer<'_> {
    #[inline(always)]
    fn parse_expr(&mut self, expr: ast::Expr) -> Expr {
        self.analyzer.parse_expr(expr)
    }
    pub fn parse_stmt(&mut self, stmt: ast::Stmt) -> Stmt {
        use ast::StmtType::*;
        use StmtType as S;

        // ugh so much boilerplate
        let data = match stmt.data {
            Compound(stmts) => {
                let mut parsed = Vec::new();
                for inner in stmts {
                    parsed.push(self.parse_stmt(inner));
                }
                S::Compound(parsed)
            }
            If(condition, then, otherwise) => {
                let condition = self
                    .parse_expr(condition)
                    .truthy(&mut self.analyzer.error_handler);
                let then = self.parse_stmt(*then);
                let otherwise = otherwise.map(|s| Box::new(self.parse_stmt(*s)));
                S::If(condition, Box::new(then), otherwise)
            }
            Do(body, condition) => {
                let body = self.parse_stmt(*body);
                let condition = self
                    .parse_expr(condition)
                    .truthy(&mut self.analyzer.error_handler);
                S::Do(Box::new(body), condition)
            }
            While(condition, body) => {
                let condition = self
                    .parse_expr(condition)
                    .truthy(&mut self.analyzer.error_handler);
                let body = self.parse_stmt(*body);
                S::While(condition, Box::new(body))
            }
            For {
                initializer,
                condition,
                post_loop,
                body,
            } => {
                let init_data = match initializer.data {
                    Expr(expr) => S::Expr(self.parse_expr(expr)),
                    Decl(decl) => {
                        let decl = self.analyzer.parse_declaration(decl, initializer.location);
                        S::Decl(decl)
                    }
                    _ => unreachable!(),
                };
                let initializer = Locatable::new(init_data, initializer.location);
                let condition = condition.map(|e| {
                    Box::new(self.parse_expr(*e).truthy(&mut self.analyzer.error_handler))
                });
                let post_loop = post_loop.map(|e| Box::new(self.parse_expr(*e)));
                let body = self.parse_stmt(*body);
                S::For(Box::new(initializer), condition, post_loop, Box::new(body))
            }
            Switch(value, body) => {
                let value = self.parse_expr(value).rval();
                if !value.ctype.is_integral() {
                    self.err(
                        SemanticError::NonIntegralSwitch(value.ctype.clone()),
                        stmt.location,
                    )
                }
                let body = self.parse_stmt(*body);
                S::Switch(value, Box::new(body))
            }
            Expr(expr) => S::Expr(self.parse_expr(expr)),
            //Label()
            _ => unimplemented!("most statements"),
            /*
            Label(InternedStr, Box<Stmt>),
            Case(u64, Box<Stmt>),
            Default(Box<Stmt>),
            Expr(Expr),
            Goto(InternedStr),
            Continue,
            Break,
            Return(Option<Expr>),
            Decl(VecDeque<Locatable<Declaration>>),
            */
        };
        Locatable::new(data, stmt.location)
    }
    /*
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
        let _guard = self.recursion_check();
        match self.peek_token() {
            Some(Token::LeftBrace) => {
                self.enter_scope();
                let stmts = self.compound_statement();
                let location = match &stmts {
                    Ok(stmt) => stmt.location,
                    Err(err) => err.location,
                };
                self.leave_scope(location);
                stmts
            }
            Some(Token::Keyword(k)) => match k {
                // labeled_statement (excluding labels)
                Keyword::Case => {
                    let kw = self.next_token().unwrap();
                    let expr = self.constant_expr()?;
                    self.expect(Token::Colon)?;
                    let int = match expr.expr {
                        ExprType::Literal(Literal::Int(i)) => i as u64,
                        ExprType::Literal(Literal::UnsignedInt(u)) => u,
                        ExprType::Literal(Literal::Char(c)) => u64::from(c),
                        _ => {
                            self.semantic_err(
                                "case expression is not an integer constant",
                                expr.location,
                            );
                            0
                        }
                    };
                    let inner = Box::new(self.statement()?);
                    Ok(Stmt {
                        data: StmtType::Case(int, inner),
                        location: kw.location,
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
                Keyword::If => Ok(self.if_statement()?),
                Keyword::Switch => Ok(self.switch_statement()?),

                // iteration_statement
                Keyword::While => Ok(self.while_statement()?),
                Keyword::Do => Ok(self.do_while_statement()?),
                Keyword::For => Ok(self.for_statement()?),

                // jump_statement
                Keyword::Goto => Ok(self.goto_statement()?),
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
                Keyword::Return => Ok(self.return_statement()?),

                // start of an expression statement
                Keyword::Sizeof
                | Keyword::StaticAssert
                | Keyword::Alignas
                | Keyword::Alignof
                | Keyword::Generic => self.expression_statement(),
                decl if decl.is_decl_specifier() => {
                    let decls = self.declaration()?;
                    let location = match decls.front() {
                        Some(decl) => decl.location,
                        None => {
                            return Ok(Stmt {
                                data: Default::default(),
                                location: self.last_location,
                            })
                        }
                    };
                    Ok(Stmt {
                        data: StmtType::Decl(decls),
                        location,
                    })
                }
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
                        Some(decl) => decl.location,
                        None => {
                            return Ok(Stmt {
                                data: Default::default(),
                                location: self.last_location,
                            })
                        }
                    };
                    Ok(Stmt {
                        data: StmtType::Decl(decls),
                        location,
                    })
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
            data: StmtType::Expr(expr),
            location: end.location,
        })
    }
    // return (expr)? ;
    fn return_statement(&mut self) -> StmtResult {
        let ret_token = self.expect(Token::Keyword(Keyword::Return)).unwrap();
        let expr = self.expr_opt(Token::Semicolon)?;
        let current = self
            .current_function
            .as_ref()
            .expect("should have current_function set when parsing statements");
        let ret_type = &current.return_type;
        let stmt = match (expr, *ret_type != Type::Void) {
            (None, false) => StmtType::Return(None),
            (None, true) => {
                let err = format!("function '{}' does not return a value", current.id);
                self.semantic_err(err, ret_token.location);
                // TODO: will this break codegen?
                StmtType::Return(None)
            }
            (Some(expr), false) => {
                let err = format!("void function '{}' should not return a value", current.id);
                self.semantic_err(err, expr.location);
                StmtType::Return(None)
            }
            (Some(expr), true) => {
                let expr = expr.rval();
                if expr.ctype != *ret_type {
                    StmtType::Return(Some(
                        Expr::cast(expr, ret_type).recover(&mut self.error_handler),
                    ))
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
        let expr = self.expr()?.rval();
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
        let condition = self.expr()?.truthy().recover(&mut self.error_handler);
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
        let condition = self.expr()?.truthy().recover(&mut self.error_handler);
        self.expect(Token::RightParen)?;
        self.expect(Token::Semicolon)?;
        let stmt = StmtType::Do(Box::new(body), condition);
        Ok(Stmt {
            data: stmt,
            location: start.location,
        })
    }
    /// for_statement:
    ///     FOR '(' expr_opt ';' expr_opt ';' expr_opt ') statement
    ///   | FOR '(' declaration expr_opt ';' expr_opt ') statement
    fn for_statement(&mut self) -> StmtResult {
        let start = self.expect(Token::Keyword(Keyword::For))?;
        let paren = self.expect(Token::LeftParen)?;
        self.enter_scope();
        let decl_stmt = match self.peek_token() {
            Some(Token::Keyword(k)) if k.is_decl_specifier() => StmtType::Decl(self.declaration()?),
            Some(Token::Id(id)) => {
                let id = *id;
                match self.scope.get(&id) {
                    Some(symbol) if symbol.storage_class == StorageClass::Typedef => {
                        StmtType::Decl(self.declaration()?)
                    }
                    _ => match self.expr_opt(Token::Semicolon)? {
                        Some(expr) => StmtType::Expr(expr),
                        None => Default::default(),
                    },
                }
            }
            Some(_) => match self.expr_opt(Token::Semicolon)? {
                Some(expr) => StmtType::Expr(expr),
                None => Default::default(),
            },
            None => {
                return Err(self
                    .last_location
                    .with(SyntaxError::EndOfFile("expression or ';'")));
            }
        };
        let decl = Box::new(Stmt {
            data: decl_stmt,
            location: paren.location,
        });
        let controlling_expr = self
            .expr_opt(Token::Semicolon)?
            .map(|expr| Expr::truthy(expr).recover(&mut self.error_handler));
        let iter_expr = self.expr_opt(Token::RightParen)?;
        let body = Box::new(self.statement()?);
        self.leave_scope(self.last_location);
        Ok(Stmt {
            data: StmtType::For(
                decl,
                controlling_expr.map(Box::new),
                iter_expr.map(Box::new),
                body,
            ),
            location: start.location,
        })
    }
    /// goto_statement: GOTO identifier ';'
    fn goto_statement(&mut self) -> StmtResult {
        let start = self.expect(Token::Keyword(Keyword::Goto)).unwrap();
        let id = match self.expect(Token::Id(Default::default()))?.data {
            Token::Id(id) => id,
            _ => unreachable!("expect should only return an Id if called with Token::Id"),
        };
        self.expect(Token::Semicolon)?;
        Ok(Stmt {
            data: StmtType::Goto(id),
            location: start.location,
        })
    }
    */
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::analyze::test::{analyze, analyze_expr};
    use crate::analyze::FunctionData;
    use crate::data::*;
    use crate::Parser;

    fn parse_stmt(stmt: &str) -> CompileResult<Stmt> {
        analyze(stmt, Parser::statement, |a, stmt| {
            let mut func_analyzer = FunctionAnalyzer {
                analyzer: a,
                metadata: FunctionData {
                    id: "<test func>".into(),
                    location: Location::default(),
                    return_type: Type::Int(true),
                },
            };
            func_analyzer.parse_stmt(stmt)
        })
    }
    #[test]
    // NOTE: this seems to be one of the few tests that checks that the location
    // is correct. If it starts failing, maybe look at the lexer first
    fn test_expr_stmt() {
        let parsed = parse_stmt("1;");
        let expected = Ok(Stmt {
            data: StmtType::Expr(analyze_expr("1").unwrap()),
            location: Location {
                file: Location::default().file,
                span: (0..2).into(),
            },
        });
        assert_eq!(parsed, expected);
        assert_eq!(parsed.unwrap().location, expected.unwrap().location);
    }
}
