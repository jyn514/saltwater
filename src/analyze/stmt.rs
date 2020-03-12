use super::FunctionAnalyzer;
use crate::data::{ast, error::SemanticError, hir::*, lex::Locatable, Location};
use crate::parse::Lexer;

impl<T: Lexer> FunctionAnalyzer<'_, T> {
    #[inline(always)]
    fn parse_expr(&mut self, expr: ast::Expr) -> Expr {
        self.analyzer.parse_expr(expr)
    }
    pub(crate) fn parse_stmt(&mut self, stmt: ast::Stmt) -> Stmt {
        use ast::StmtType::*;
        use StmtType as S;

        // ugh so much boilerplate
        let data = match stmt.data {
            Compound(stmts) => {
                // 6.2.1 Scopes of identifiers
                self.enter_scope();
                let mut parsed = Vec::new();
                for inner in stmts {
                    parsed.push(self.parse_stmt(inner));
                }
                self.leave_scope(stmt.location);
                S::Compound(parsed)
            }
            // 6.8.3 Expression and null statements
            Expr(expr) => S::Expr(self.parse_expr(expr)),
            // 6.8.4.1 The if statement
            If(condition, then, otherwise) => {
                let condition = self
                    .parse_expr(condition)
                    .truthy(&mut self.analyzer.error_handler);
                let then = self.parse_stmt(*then);
                let otherwise = otherwise.map(|s| Box::new(self.parse_stmt(*s)));
                S::If(condition, Box::new(then), otherwise)
            }
            // 6.8.4.2 The switch statement
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
            // 6.8.5.2 The do statement
            Do(body, condition) => {
                let body = self.parse_stmt(*body);
                let condition = self
                    .parse_expr(condition)
                    .truthy(&mut self.analyzer.error_handler);
                S::Do(Box::new(body), condition)
            }
            // 6.8.5.1 The while statement
            While(condition, body) => {
                let condition = self
                    .parse_expr(condition)
                    .truthy(&mut self.analyzer.error_handler);
                let body = self.parse_stmt(*body);
                S::While(condition, Box::new(body))
            }
            // 6.8.5.3 The for statement
            For {
                initializer,
                condition,
                post_loop,
                body,
            } => {
                // TODO: maybe a sanity check here that the init statement is only an expression or declaration?
                // Or encode that in the type somehow?
                self.enter_scope();
                let initializer = self.parse_stmt(*initializer);
                let condition = condition.map(|e| {
                    Box::new(self.parse_expr(*e).truthy(&mut self.analyzer.error_handler))
                });
                let post_loop = post_loop.map(|e| Box::new(self.parse_expr(*e)));
                let body = self.parse_stmt(*body);
                self.leave_scope(stmt.location);
                S::For(Box::new(initializer), condition, post_loop, Box::new(body))
            }
            // 6.8.1 Labeled statements
            // TODO: all of these should have semantic checking here, not in the backend
            Label(name, inner) => {
                let inner = self.parse_stmt(*inner);
                S::Label(name, Box::new(inner))
            }
            Case(expr, inner) => self.case_statement(*expr, *inner, stmt.location),
            // 6.8.1 Labeled statements
            Default(inner) => S::Default(Box::new(self.parse_stmt(*inner))),
            // 6.8.6.1 The goto statement
            Goto(label) => S::Goto(label),
            // 6.8.6.2 The continue statement
            Continue => S::Continue,
            // 6.8.6.3 The break statement
            Break => S::Break,
            Return(value) => self.return_statement(value, stmt.location),
            // 6.7 Declarations
            Decl(decls) => S::Decl(self.analyzer.parse_declaration(decls, stmt.location)),
        };
        let data = if !self.analyzer.decl_side_channel.is_empty() {
            let decls = std::mem::replace(&mut self.analyzer.decl_side_channel, Vec::new());
            // this location is wrong for the declarations, but it's _probably_ fine
            let decl_stmt = Stmt::new(S::Decl(decls), stmt.location);
            S::Compound(vec![decl_stmt, Stmt::new(data, stmt.location)])
        } else {
            data
        };
        Locatable::new(data, stmt.location)
    }
    // 6.8.1 Labeled statements
    fn case_statement(
        &mut self,
        expr: ast::Expr,
        inner: ast::Stmt,
        location: Location,
    ) -> StmtType {
        use super::expr::literal;
        use crate::data::lex::Literal;

        let expr = match self.parse_expr(expr).const_fold(&self.analyzer.target) {
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
    // 6.8.6.4 The return statement
    // A value of `None` for `expr` means `return;`
    fn return_statement(&mut self, expr: Option<ast::Expr>, location: Location) -> StmtType {
        use crate::data::Type;

        let expr = expr.map(|e| self.parse_expr(e));
        let ret_type = &self.metadata.return_type;
        match (expr, *ret_type != Type::Void) {
            // void f() { return ;}
            (None, false) => StmtType::Return(None),
            // int f() { return; }
            (None, true) => {
                self.err(
                    SemanticError::MissingReturnValue(self.metadata.id),
                    location,
                );
                StmtType::Return(None)
            }
            // void f() { return 1; }
            (Some(expr), false) => {
                self.err(
                    SemanticError::ReturnFromVoid(self.metadata.id),
                    expr.location,
                );
                StmtType::Return(None)
            }
            // int f() { return 1; }
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
