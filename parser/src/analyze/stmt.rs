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
                self.enter_scope();
                let mut parsed = Vec::new();
                for inner in stmts {
                    parsed.push(self.parse_stmt(inner));
                }
                self.leave_scope(stmt.location);
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
            Return(value) => self.return_statement(value, stmt.location),
            Label(name, inner) => {
                let inner = self.parse_stmt(*inner);
                S::Label(name, Box::new(inner))
            }
            Case(expr, inner) => self.case_statement(*expr, *inner, stmt.location),
            _ => unimplemented!("most statements"),
            /*
            Default(Box<Stmt>),
            Goto(InternedStr),
            Continue,
            Break,
            Decl(VecDeque<Locatable<Declaration>>),
            */
        };
        Locatable::new(data, stmt.location)
    }
    fn case_statement(
        &mut self, expr: ast::Expr, inner: ast::Stmt, location: Location,
    ) -> StmtType {
        use super::expr::literal;
        use crate::data::hir::Expr;
        use crate::data::lex::Literal;

        let expr = match self.parse_expr(expr).const_fold() {
            Ok(e) => e,
            Err(err) => {
                self.analyzer.error_handler.push_back(err);
                Expr::zero(location)
            }
        };
        let int = match expr.into_literal() {
            Ok(Literal::Int(i)) => i as u64,
            Ok(Literal::UnsignedInt(u)) => u,
            Ok(Literal::Char(c)) => c.into(),
            Ok(other) => {
                let ctype = literal(other, location).ctype;
                self.err(SemanticError::NonIntegralExpr(ctype), location);
                0
            }
            Err(other) => {
                self.err(SemanticError::NotConstant(other), location);
                0
            }
        };
        let inner = self.parse_stmt(inner);
        StmtType::Case(int, Box::new(inner))
    }
    fn return_statement(&mut self, expr: Option<ast::Expr>, location: Location) -> StmtType {
        use crate::data::Type;

        let expr = expr.map(|e| self.parse_expr(e));
        let ret_type = &self.metadata.return_type;
        match (expr, *ret_type != Type::Void) {
            (None, false) => StmtType::Return(None),
            (None, true) => {
                let err = format!("function '{}' does not return a value", self.metadata.id);
                self.err(
                    SemanticError::MissingReturnValue(self.metadata.id),
                    location,
                );
                StmtType::Return(None)
            }
            (Some(expr), false) => {
                self.err(
                    SemanticError::ReturnFromVoid(self.metadata.id),
                    expr.location,
                );
                StmtType::Return(None)
            }
            (Some(expr), true) => {
                let expr = expr.rval();
                if expr.ctype != *ret_type {
                    StmtType::Return(Some(
                        expr.implicit_cast(ret_type, &mut self.analyzer.error_handler),
                    ))
                } else {
                    StmtType::Return(Some(expr))
                }
            }
        }
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
