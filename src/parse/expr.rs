use super::{Lexeme, Parser};
use crate::data::*;

type ExprResult = Result<Expr, Locatable<String>>;

impl<I: Iterator<Item = Lexeme>> Parser<I> {
    /// expr(): Parse an expression.
    ///
    /// In programming language terminology, an 'expression' is anything that has a value.
    /// This can be a literal, a function call, or a series of operations like `2 + 3`.
    /// You can think of it as anything you can put on the right-hand side of an assignment.
    /// Contrast expressions to statements, which do NOT have values: you can't assign a while loop.
    ///
    /// For more discussion on the difference between expressions and statements,
    /// see https://stackoverflow.com/a/19224 or an introductory programming textbook
    /// (it will be discussed in the first few chapters,
    /// in a part of the book no one usually reads).
    // Original:
    // expr:
    //      assignment_expr
    //      | expr ',' assignment_expr
    //      ;
    //
    // We rewrite it as follows:
    // expr:
    //     assignment_expr (',' assignment_expr)*
    //     ;
    //
    // Comma operator: evalutate the first expression (usually for its side effects)
    // and return the second
    pub fn expr(&mut self) -> ExprResult {
        self.left_associative_binary_op(
            Self::assignment_expr,
            &[&Token::Comma],
            |left, right, token| {
                Ok(Expr {
                    ctype: right.ctype.clone(),
                    // TODO: this is technically right but will almost certainly be buggy
                    // If we use constexpr to check if we can optimize things out,
                    // then we'll discard all side effects from `left`.
                    // That's not really `expr()`'s problem, but it is something the constant
                    // folding has to worry about
                    constexpr: right.constexpr,
                    lval: right.lval,
                    expr: ExprType::Comma(left, right),
                    location: token.location,
                })
            },
        )
    }

    /// Parses an expression and ensures that it can be evaluated at compile time.
    // constant_expr: conditional_expr;
    pub fn constant_expr(&mut self) -> ExprResult {
        let expr = self.conditional_expr()?;
        if expr.constexpr {
            Ok(expr)
        } else {
            Err(Locatable {
                data: "not a constant expression".to_string(),
                location: expr.location,
            })
        }
    }

    /// assignment_expr
    /// : conditional_expr
    /// | unary_expr assignment_operator assignment_expr
    /// ;
    ///
    /// Assignment expression: evaluate the right-hand side, assign it to the left,
    /// and return the right.
    ///
    /// Unlike most operators, this is right-associative, that is
    /// `a = b = 3` is parsed as `a = (b = 3)`. Contrast addition:
    /// `a + b + 3` is parsed as `(a + b) + 3`.
    ///
    /// NOTE: because it's hard to tell the different between lvals and rvals in the grammar,
    /// we parse an entire expression, see if an assignment operator follows it,
    /// and only then check if the left is an lval.
    /// NOTE: comma operators aren't allowed on the RHS of an assignment.
    fn assignment_expr(&mut self) -> ExprResult {
        let lval = self.conditional_expr()?;
        if self
            .peek_token()
            .map_or(false, Token::is_assignment_operator)
        {
            let assign_op = self.next_token().unwrap();
            let rval = self.assignment_expr()?;
            if !lval.lval {
                Err(Locatable {
                    data: "expression is not assignable".to_string(),
                    location: assign_op.location,
                })
            } else {
                Ok(Expr {
                    ctype: lval.ctype.clone(),
                    constexpr: rval.constexpr,
                    lval: false, // `(i = j) = 4`; is invalid
                    location: assign_op.location,
                    expr: ExprType::Assign(Box::new(lval), Box::new(rval), assign_op.data),
                })
            }
        } else {
            Ok(lval)
        }
    }

    /// conditional_expr
    /// : logical_or_expr
    /// | logical_or_expr '?' expr ':' conditional_expr
    /// ;
    ///
    /// Ternary operator. If logical_or_expr evaluates to true,
    /// evaluates to `expr`, otherwise evaluates to `conditional_expr`.
    /// This is the analog to `if` statements for expressions.
    ///
    /// Note that comma operators are allowed within ternaries (!!).
    ///
    /// The C standard requires that `expr` and `conditional_expr` have compatible types;
    /// see https://stackoverflow.com/questions/13318336/ or section 6.5.15 of
    /// http://www.open-std.org/jtc1/sc22/wg14/www/docs/n1570.pdf for formal requirements.
    /// It does not specify what happens if this is not the case.
    /// Clang and GCC give a warning; we are more strict and emit an error.
    fn conditional_expr(&mut self) -> ExprResult {
        let condition = self.logical_or_expr()?;
        if let Some(Locatable { location, .. }) = self.match_next(&Token::Question) {
            let then = self.expr()?;
            self.expect(Token::Colon);
            let otherwise = self.conditional_expr()?;
            if then.ctype == otherwise.ctype {
                Ok(Expr {
                    ctype: then.ctype.clone(),
                    // TODO: evaluate condition and only require the corresponding
                    // expression to be constexpr
                    constexpr: condition.constexpr && then.constexpr && otherwise.constexpr,
                    lval: false,
                    location,
                    expr: ExprType::Ternary(
                        Box::new(condition),
                        Box::new(then),
                        Box::new(otherwise),
                    ),
                })
            } else {
                Err(Locatable {
                    data: format!(
                        "incompatible types in ternary expression: '{}' cannot be converted to '{}'",
                        then.ctype, otherwise.ctype
                    ),
                    location,
                })
            }
        } else {
            Ok(condition)
        }
    }

    /// Original:
    /// logical_or_expr
    /// : logical_and_expr
    /// | logical_or_expr OR_OP logical_and_expr
    /// ;
    ///
    /// Rewritten:
    /// logical_or_expr:
    ///     logical_and_expr (OR_OP logical_and_expr)*
    ///
    /// A logical or ('||') evaluates the left-hand side. If the left is falsy, it evaluates and
    /// returns the right-hand side as a boolean.
    /// Both the left and right hand sides must be scalar types.
    fn logical_or_expr(&mut self) -> ExprResult {
        self.scalar_left_associative_binary_op(
            Self::logical_and_expr,
            ExprType::LogicalOr,
            &Token::LogicalOr,
            Type::Bool,
        )
    }

    /// logical_and_expr
    /// : inclusive_or_expr
    /// | logical_and_expr AND_OP inclusive_or_expr
    /// ;
    ///
    /// Rewritten:
    /// logical_and_expr:
    ///     inclusive_or_expr (AND_OP inclusive_or_expr)*
    ///
    /// A logical and ('&&') evaluates the left-hand side. If the left is truthy, it evaluates
    /// and returns the right-hand side as a boolean.
    /// Both the left and right hand sides must be scalar types.
    fn logical_and_expr(&mut self) -> ExprResult {
        self.scalar_left_associative_binary_op(
            Self::inclusive_or_expr,
            ExprType::LogicalAnd,
            &Token::LogicalAnd,
            Type::Bool,
        )
    }

    /// inclusive_or_expr
    /// : exclusive_or_expr
    /// | inclusive_or_expr '|' exclusive_or_expr
    /// ;
    ///
    /// Rewritten similarly.
    fn inclusive_or_expr(&mut self) -> ExprResult {
        self.integral_left_associative_binary_op(
            Self::exclusive_or_expr,
            &[&Token::BinaryOr],
            default_expr(ExprType::BitwiseOr),
        )
    }

    /// exclusive_or_expr
    /// : and_expr
    /// | exclusive_or_expr '^' and_expr
    /// ;
    fn exclusive_or_expr(&mut self) -> ExprResult {
        self.integral_left_associative_binary_op(
            Self::and_expr,
            &[&Token::Xor],
            default_expr(ExprType::Xor),
        )
    }

    /// and_expr
    /// : equality_expr
    /// | and_expr '&' equality_expr
    /// ;
    fn and_expr(&mut self) -> ExprResult {
        self.integral_left_associative_binary_op(
            Self::equality_expr,
            &[&Token::Ampersand],
            default_expr(ExprType::BitwiseAnd),
        )
    }

    /// equality_expr
    /// : relational_expr
    /// | equality_expr EQ_OP relational_expr
    /// | equality_expr NE_OP relational_expr
    /// ;
    fn equality_expr(&mut self) -> ExprResult {
        self.left_associative_binary_op(
            Self::relational_expr,
            &[&Token::EqualEqual, &Token::NotEqual],
            relational_expr,
        )
    }

    /// relational_expr
    /// : shift_expr
    /// | relational_expr '<' shift_expr
    /// | relational_expr '>' shift_expr
    /// | relational_expr LE_OP shift_expr
    /// | relational_expr GE_OP shift_expr
    /// ;
    fn relational_expr(&mut self) -> ExprResult {
        self.left_associative_binary_op(
            Self::shift_expr,
            &[
                &Token::Less,
                &Token::Greater,
                &Token::LessEqual,
                &Token::GreaterEqual,
            ],
            relational_expr,
        )
    }

    /// shift_expr
    /// : additive_expr
    /// | shift_expr LEFT_OP additive_expr
    /// | shift_expr RIGHT_OP additive_expr
    /// ;
    fn shift_expr(&mut self) -> ExprResult {
        self.integral_left_associative_binary_op(
            Self::additive_expr,
            &[&Token::ShiftLeft, &Token::ShiftRight],
            |left, right, token| {
                Ok(Expr {
                    ctype: left.ctype.clone(),
                    location: token.location,
                    lval: false,
                    constexpr: left.constexpr && right.constexpr,
                    expr: ExprType::Shift(left, right, token.data == Token::ShiftLeft),
                })
            },
        )
    }

    /// additive_expr
    /// : multiplicative_expr
    /// | additive_expr '+' multiplicative_expr
    /// | additive_expr '-' multiplicative_expr
    /// ;
    fn additive_expr(&mut self) -> ExprResult {
        self.left_associative_binary_op(
            Self::multiplicative_expr,
            &[&Token::Plus, &Token::Minus],
            |left, right, token| {
                Ok(Expr {
                    ctype: left.ctype.clone(),
                    location: token.location,
                    lval: false,
                    constexpr: left.constexpr && right.constexpr,
                    expr: (if token.data == Token::Plus {
                        ExprType::Add
                    } else {
                        ExprType::Sub
                    })(left, right),
                })
            },
        )
    }

    /// multiplicative_expr
    /// : cast_expr
    /// | multiplicative_expr '*' cast_expr
    /// | multiplicative_expr '/' cast_expr
    /// | multiplicative_expr '%' cast_expr
    /// ;
    fn multiplicative_expr(&mut self) -> ExprResult {
        self.left_associative_binary_op(
            Self::cast_expr,
            &[&Token::Star, &Token::Divide, &Token::Mod],
            |left, right, token| {
                let ctype = Type::binary_promote(&left.ctype, &right.ctype);
                let type_bound = if token.data == Token::Mod {
                    Type::is_integral
                } else {
                    Type::is_arithmetic
                };
                if type_bound(&ctype) {
                    Ok(Expr {
                        ctype,
                        location: token.location,
                        constexpr: left.constexpr && right.constexpr,
                        lval: false,
                        expr: match token.data {
                            Token::Star => ExprType::Mul(left, right),
                            Token::Divide => ExprType::Div(left, right),
                            Token::Mod => ExprType::Mod(left, right),
                            _ => panic!(
                                "left_associate_binary_op should only return tokens given to it"
                            ),
                        },
                    })
                } else {
                    Err(Locatable {
                        location: token.location,
                        data: format!(
                            "expected {} for both operands of '{}' , got {}",
                            if token.data == Token::Mod {
                                "integer"
                            } else {
                                "number"
                            },
                            token.data,
                            ctype
                        ),
                    })
                }
            },
        )
    }

    /// cast_expr
    /// : unary_expr
    /// | '(' type_name ')' cast_expr
    /// ;
    fn cast_expr(&mut self) -> ExprResult {
        if self.peek_token() == Some(&Token::LeftParen) {
            match self.peek_next_token() {
                Some(Token::Keyword(k)) if k.is_decl_specifier() => {
                    self.next_token();
                    let ctype = self.type_name()?;
                    self.expect(Token::RightParen);
                    let right = self.cast_expr()?;
                    unimplemented!("casts are not implemented")
                }
                _ => self.unary_expr(),
            }
        } else {
            self.unary_expr()
        }
    }

    /// unary_expr
    /// : postfix_expr
    /// | INC_OP unary_expr
    /// | DEC_OP unary_expr
    /// | unary_operator cast_expr
    /// | SIZEOF unary_expr
    /// | SIZEOF '(' type_name ')'
    /// ;
    fn unary_expr(&mut self) -> ExprResult {
        match self.peek_token() {
            Some(Token::PlusPlus) => {
                let Locatable { location, .. } = self.next_token().unwrap();
                let expr = self.unary_expr()?;
                increment_op(true, true, expr, location)
            }
            Some(Token::MinusMinus) => {
                let Locatable { location, .. } = self.next_token().unwrap();
                let expr = self.unary_expr()?;
                increment_op(true, false, expr, location)
            }
            Some(Token::Keyword(Keyword::Sizeof)) => {
                self.next_token();
                let (location, ctype) = if self.match_next(&Token::LeftParen).is_some() {
                    let result = self.type_name()?;
                    (result.location, result.data)
                } else {
                    let result = self.unary_expr()?;
                    (result.location, result.ctype)
                };
                Ok(Expr {
                    // the C11 standard states (6.5.3.4)
                    // "If the type of the operand is a variable length array type, the operand is evaluated; otherwise, the operand is not evaluated and the result is an integer constant."
                    // In an example, it states that the following code would perform
                    // an 'execution time `sizeof`':
                    // int f(int n) {
                    //   char b[n+3];
                    //   return sizeof b;
                    // }
                    // We do not currently handle this case.
                    constexpr: true,
                    expr: ExprType::Sizeof(ctype),
                    lval: false,
                    location,
                    ctype: Type::Int(true),
                })
            }
            Some(op) if op.is_unary_operator() => {
                let Locatable { location, data: op } = self.next_token().unwrap();
                let expr = self.cast_expr();
                match op {
                    Token::Ampersand => unimplemented!("address of"),
                    Token::Star => unimplemented!("dereference"),
                    Token::Plus => unimplemented!("unary plus, does nothing but make it an rval"),
                    Token::Minus => unimplemented!("unary minus"),
                    Token::BinaryNot => unimplemented!("binary not"),
                    Token::LogicalNot => unimplemented!("logical not"),
                    x => panic!("didn't expect '{}' to be an unary operand", x),
                }
            }
            _ => self.postfix_expr(),
        }
    }

    /// postfix_expr
    /// : primary_expr
    /// | postfix_expr '[' expr ']'
    /// | postfix_expr '(' argument_expr_list_opt ')'
    /// | postfix_expr '.' identifier
    /// | postfix_expr PTR_OP identifier
    /// | postfix_expr INC_OP
    /// | postfix_expr DEC_OP
    /// ;
    fn postfix_expr(&mut self) -> ExprResult {
        let expr = self.primary_expr()?;
        if let Some(Locatable {
            location,
            data: token,
        }) = self.next_token()
        {
            match token {
                Token::LeftBracket => unimplemented!("TODO: array indexing"),
                Token::LeftParen => {
                    let args = self.argument_expr_list_opt();
                    self.expect(Token::RightParen);
                    unimplemented!("TODO: function calls");
                }
                Token::Dot => {
                    let member = self.expect(Token::Id(Default::default()));
                    unimplemented!("structs are very much not implemented");
                }
                Token::StructDeref => {
                    let member = self.expect(Token::Id(Default::default()));
                    unimplemented!("structs are very much not implemented");
                }
                Token::PlusPlus => {
                    let Locatable { location, .. } = self.next_token().unwrap();
                    increment_op(false, true, expr, location)
                }
                Token::MinusMinus => {
                    let Locatable { location, .. } = self.next_token().unwrap();
                    increment_op(false, false, expr, location)
                }
                _ => {
                    self.unput(Some(Locatable {
                        location,
                        data: token,
                    }));
                    Ok(expr)
                }
            }
        } else {
            Ok(expr)
        }
    }

    /// argument_expr_list_opt
    /// : /* empty */
    /// | assignment_expr (',' assignment_expr)*
    /// ;
    fn argument_expr_list_opt(&mut self) -> Vec<ExprResult> {
        if self.peek_token() == Some(&Token::RightParen) {
            return vec![];
        }
        let mut args = vec![self.assignment_expr()];
        while self.match_next(&Token::Comma).is_some() {
            args.push(self.assignment_expr());
        }
        args
    }

    /// primary_expr
    /// : identifier
    /// | INT_CONSTANT
    /// | DOUBLE_CONSTANT
    /// | STRING_LITERAL
    /// | '(' expr ')'
    /// ;
    fn primary_expr(&mut self) -> ExprResult {
        use Token::*;
        if let Some(Locatable { location, data }) = self.next_token() {
            match data {
                Id(name) => match self.scope.get(&name) {
                    None => Err(Locatable {
                        location,
                        data: format!("use of undeclared identifier '{}'", name),
                    }),
                    Some(symbol) => Ok(Expr {
                        // TODO: this clone will get expensive fast
                        expr: ExprType::Id(symbol.clone()),
                        // TODO: check if symbol is constexpr
                        // in particular, I would love for this to compile:
                        // `int a = 5; int b[a];`
                        // NOTE: neither GCC nor Clang accept that
                        constexpr: false,
                        ctype: symbol.ctype.clone(),
                        lval: true,
                        location,
                    }),
                },
                Str(literal) => Ok(string_literal(literal, location)),
                Int(literal) => Ok(int_literal(literal, location)),
                Float(literal) => Ok(float_literal(literal, location)),
                LeftParen => {
                    let expr = self.expr();
                    self.expect(RightParen);
                    expr
                }
                other => {
                    let err = Err(Locatable {
                        location: location.clone(),
                        data: format!("expected '(' or literal, got '{}'", other),
                    });
                    self.unput(Some(Locatable {
                        location,
                        data: other,
                    }));
                    err
                }
            }
        } else {
            Err(Locatable {
                location: self.next_location().clone(),
                data: "expected '(' or literal, got <end-of-file>".to_string(),
            })
        }
    }

    /// Parse a grammar rule of the form
    /// rule:
    ///     grammar_item (TOKEN grammar_item)*
    ///
    /// which requires its operands to be scalar.
    ///
    /// next_grammar_func should parse `grammar_item`.
    /// `expr_func` is usually an Enum constructor.
    /// `token` should be the token for the operation.
    /// `ctype` should be the type of the resulting expression (_not_ the operands).
    fn scalar_left_associative_binary_op<E, G>(
        &mut self,
        next_grammar_func: G,
        expr_func: E,
        token: &Token,
        ctype: Type,
    ) -> ExprResult
    where
        E: Fn(Box<Expr>, Box<Expr>) -> ExprType,
        G: Fn(&mut Self) -> ExprResult,
    {
        self.left_associative_binary_op(next_grammar_func, &[token], move |left, right, token| {
            let non_scalar = if !left.ctype.is_scalar() {
                Some(left.ctype.clone())
            } else if !right.ctype.is_scalar() {
                Some(right.ctype.clone())
            } else {
                None
            };
            if let Some(ctype) = non_scalar {
                return Err(Locatable {
                    data: format!(
                        "expected scalar type (number or pointer) for both operands of '{}', got '{}'",
                        token.data, ctype
                    ),
                    location: token.location,
                });
            }
            Ok(Expr {
                lval: false,
                constexpr: left.constexpr && right.constexpr,
                location: token.location,
                ctype: ctype.clone(),
                expr: expr_func(left, right),
            })
        })
    }

    /// Parse a grammar rule of the form
    /// rule:
    ///     grammar_item (TOKEN grammar_item)*
    ///
    /// which requires its operands to be integral.
    /// The type of the resulting expression will be the same as that of its inputs.
    ///
    /// next_grammar_func should parse `grammar_item`.
    /// `expr_func` is usually an Enum constructor.
    fn integral_left_associative_binary_op<E, G>(
        &mut self,
        next_grammar_func: G,
        tokens: &[&Token],
        expr_func: E,
    ) -> ExprResult
    where
        E: Fn(Box<Expr>, Box<Expr>, Locatable<Token>) -> ExprResult,
        G: Fn(&mut Self) -> ExprResult,
    {
        self.left_associative_binary_op(next_grammar_func, tokens, |expr, next, token| {
            let non_scalar = if !expr.ctype.is_integral() {
                Some(expr.ctype.clone())
            } else if !next.ctype.is_integral() {
                Some(next.ctype.clone())
            } else {
                None
            };
            if let Some(ctype) = non_scalar {
                return Err(Locatable {
                    data: format!(
                        "expected integer on both sides of '{}', got '{}'",
                        token.data, ctype
                    ),
                    location: token.location,
                });
            }
            expr_func(expr, next, token)
        })
    }

    /// Parse a grammar rule of the form
    /// rule:
    ///     grammar_item (TOKEN grammar_item)*
    ///
    /// next_grammar_func should parse `grammar_item`.
    /// `token` should be the token for the operation.
    /// `expr_func` is called with the arguments (grammar_item, grammar_item, TOKEN)
    /// to allow maximum flexibility. If you want convenience instead,
    /// consider `scalar_left_associative_binary_op` or `left_associative_binary_op`
    #[inline]
    fn left_associative_binary_op<E, G>(
        &mut self,
        next_grammar_func: G,
        tokens: &[&Token],
        expr_func: E,
    ) -> ExprResult
    where
        E: Fn(Box<Expr>, Box<Expr>, Locatable<Token>) -> ExprResult,
        G: Fn(&mut Self) -> ExprResult,
    {
        let mut expr = next_grammar_func(self)?;
        while let Some(locatable) = self.match_any(tokens) {
            let next = next_grammar_func(self)?;
            expr = expr_func(Box::new(expr), Box::new(next), locatable)?;
        }
        Ok(expr)
    }
}

/* stateless helper functions */

fn increment_op(prefix: bool, increment: bool, expr: Expr, location: Location) -> ExprResult {
    if !expr.is_modifiable_lval() {
        Err(Locatable {
            location: expr.location,
            data: "expression is not assignable".to_string(),
        })
    } else if !(expr.ctype.is_arithmetic() || expr.ctype.is_pointer()) {
        Err(Locatable {
            location: expr.location,
            data: format!(
                "cannot increment or decrement value of type '{}'",
                expr.ctype
            ),
        })
    } else {
        Ok(Expr {
            constexpr: expr.constexpr,
            lval: true,
            ctype: expr.ctype.clone(),
            // true, false: pre-decrement
            expr: ExprType::Increment(Box::new(expr), prefix, increment),
            location,
        })
    }
}

// convenience method for constructing an Expr
fn default_expr<C>(constructor: C) -> impl Fn(Box<Expr>, Box<Expr>, Locatable<Token>) -> ExprResult
where
    C: Fn(Box<Expr>, Box<Expr>) -> ExprType,
{
    move |left: Box<Expr>, right: Box<Expr>, token: Locatable<Token>| {
        Ok(Expr {
            location: token.location,
            ctype: left.ctype.clone(),
            constexpr: left.constexpr && right.constexpr,
            lval: false,
            expr: constructor(left, right),
        })
    }
}

// helper function since == and > have almost identical logic
fn relational_expr(left: Box<Expr>, right: Box<Expr>, token: Locatable<Token>) -> ExprResult {
    // TODO: binary promote operands
    Ok(Expr {
        constexpr: left.constexpr && right.constexpr,
        lval: false,
        location: token.location,
        ctype: Type::Bool,
        expr: ExprType::Compare(left, right, token.data),
    })
}

// this and the next few '*_literal' functions make unit tests more convenient
fn int_literal(value: i64, location: Location) -> Expr {
    literal(
        Type::Int(true),
        location,
        ExprType::Literal(Token::Int(value)),
    )
}

fn float_literal(value: f64, location: Location) -> Expr {
    literal(
        Type::Float,
        location,
        ExprType::Literal(Token::Float(value)),
    )
}

fn string_literal(value: String, location: Location) -> Expr {
    literal(
        Type::for_string_literal(value.len()),
        location,
        ExprType::Literal(Token::Str(value)),
    )
}

fn literal(ctype: Type, location: Location, expr: ExprType) -> Expr {
    Expr {
        constexpr: true,
        lval: false,
        ctype,
        location,
        expr,
    }
}

impl Token {
    fn is_unary_operator(&self) -> bool {
        match self {
            Token::Ampersand
            | Token::Star
            | Token::Plus
            | Token::Minus
            | Token::BinaryNot
            | Token::LogicalNot => true,
            _ => false,
        }
    }
    fn is_assignment_operator(&self) -> bool {
        use Token::*;
        match self {
            Equal | PlusEqual | MinusEqual | StarEqual | DivideEqual | ModEqual | LeftEqual
            | RightEqual | AndEqual | OrEqual | XorEqual => true,
            _ => false,
        }
    }
}

impl Expr {
    /// See section 6.3.2.1 of the C Standard. In particular:
    /// "A modifiable lvalue is an lvalue that does not have array type,
    /// does not  have an incomplete type, does not have a const-qualified type,
    /// and if it is a structure or union, does not have any member with a const-qualified type"
    fn is_modifiable_lval(&self) -> bool {
        if !self.lval {
            return false;
        }
        match &self.expr {
            // p = 5;
            ExprType::Id(sym) => sym.qualifiers.c_const,
            // *p = 1;
            ExprType::Deref(_) => match &self.ctype {
                Type::Pointer(_, quals) => quals.c_const,
                _ => panic!("only pointers can be dereferenced"),
            },
            _ => unimplemented!("what's an lval but not a pointer or id?"),
        }
    }
    // Convert an expression to _Bool. Section 6.3.1.3 of the C standard:
    // "When any scalar value is converted to _Bool,
    // the result is 0 if the value compares equal to 0; otherwise, the result is 1."
    fn truthy(expr: Expr) -> Expr {
        Expr {
            constexpr: expr.constexpr,
            lval: false,
            location: expr.location.clone(),
            ctype: Type::Int(true),
            expr: ExprType::Compare(Box::new(expr), Box::new(zero()), Token::NotEqual),
        }
    }
}

/// Implicit conversions.
/// These are handled here and no other part of the compiler deals with them directly.
impl Type {
    pub fn integer_promote(from: Type, to: Type) -> Result<Type, ()> {
        if !(from.is_integral() && to.is_integral()) {
            Err(())
        } else if from.rank() >= to.rank() {
            Ok(from)
        } else {
            Ok(to)
        }
    }
    /// Perform the 'usual arithmetic conversions' from 6.3.1.8 of the C standard.
    ///
    /// Algorithm:
    /// If either object is a `double`, convert the other to a double.
    /// Else if either is a `float`, convert the other to a float.
    /// Else if both are signed or both are unsigned, convert the object with lesser rank to
    /// the type of the object with greater rank.
    /// Else if the unsigned object has rank >= other, convert other -> unsigned version (!!).
    /// Else if signed type can represent all values of the unsigned type,
    /// convert unsigned -> signed.
    /// Else, convert signed -> unsigned.
    ///
    /// The exclamation marks are because the following will evaluate to MAX_UINT,
    /// _not_ -1: `1ul + (short)-2`.
    ///
    /// Trying to promote derived types (pointers, functions, etc.) is an error.
    /// Pointer arithmetic should not promote either argument, see 6.5.6 of the C standard.
    fn binary_promote(left: &Type, right: &Type) -> Type {
        use Type::*;
        if *left == Double || *right == Double {
            return Double; // toil and trouble
        } else if *left == Float || *right == Float {
            return Float;
        }
        let signs = (left.sign(), right.sign());
        // same sign
        if signs.0 == signs.1 {
            return if left.rank() >= right.rank() {
                left.clone()
            } else {
                right.clone()
            };
        };
        let (signed, unsigned) = if signs.0 {
            (left, right)
        } else {
            (right, left)
        };
        if signed.can_represent(&unsigned) {
            signed.clone()
        } else {
            unsigned.clone()
        }
    }
    /// Return whether self is a signed type.
    ///
    /// Should only be called on integral types.
    /// Calling sign() on a floating or derived type will panic.
    fn sign(&self) -> bool {
        use Type::*;
        match self {
            Char(sign) | Short(sign) | Int(sign) | Long(sign) => *sign,
            Bool => false,
            _ => panic!("Type::sign can only be called on integral types"),
        }
    }
    /// Return the rank of an integral type, according to section 6.3.1.1 of the C standard.
    ///
    /// It is an error to take the rank of a non-integral type.
    ///
    /// Examples:
    /// ```
    /// use data::Type::*;
    /// assert!(Long.rank() > Int.rank());
    /// assert!(Int.rank() > Short.rank());
    /// assert!(Short.rank() > Char.rank());
    /// assert!(Char.rank() > Bool.rank());
    /// assert!(Long.rank() > Bool.rank());
    /// ```
    fn rank(&self) -> usize {
        use Type::*;
        match self {
            Bool => 0,
            Char(_) => 1,
            Short(_) => 2,
            Int(_) => 3,
            Long(_) => 4,
            // don't make this 5 in case we add `long long` at some point
            _ => std::usize::MAX,
        }
    }
    fn for_string_literal(len: usize) -> Type {
        // int overflow should never happen, nobody makes strings that
        // are 2^64 characters long. it wouldn't even fit onto disk!
        Type::Array(
            Box::new(Type::Char(true)),
            ArrayType::Fixed(Box::new(int_literal(len as i64, Default::default()))),
        )
    }
}

#[cfg(test)]
mod tests {
    use crate::data::*;
    use crate::parse::expr::ExprResult;
    use crate::parse::tests::*;
    use crate::{Lexer, Parser};
    fn parse_expr(input: &str) -> ExprResult {
        // because we're a child module of parse, we can skip straight to `expr()`
        Parser::new(Lexer::new("<test-suite>".to_string(), input.chars())).expr()
    }
    fn get_location(expr: &ExprResult) -> Location {
        match expr {
            Err(_) => Default::default(),
            Ok(ref l) => l.location.clone(),
        }
    }
    fn test_literal<C: std::string::ToString, T>(token: C, parse_literal: T) -> bool
    where
        T: Fn(C, Location) -> Expr,
    {
        let parsed = parse_expr(&token.to_string());
        parsed == Ok(parse_literal(token, get_location(&parsed)))
    }
    #[test]
    fn test_primaries() {
        assert!(test_literal(141, super::int_literal));
        let parsed = parse_expr("\"hi there\"");
        assert!(
            parsed
                == Ok(super::string_literal(
                    "hi there\0".to_string(),
                    get_location(&parsed)
                ))
        );
        assert!(test_literal(1.5, super::float_literal));
        let parsed = parse_expr("(1)");
        assert!(parsed == Ok(super::int_literal(1, get_location(&parsed))));
        let parsed = parse_expr("x");
    }
    #[test]
    fn test_mul() {
        assert!(parse_expr("1*1.0").unwrap().ctype == Type::Float);
        assert!(parse_expr("1*2.0 / 1.3").unwrap().ctype == Type::Float);
        assert!(parse_expr("3%2").unwrap().ctype == Type::Int(true));
    }
    #[test]
    fn test_type_errors() {
        assert!(parse_expr("1 % 2.0").is_err());
    }
}
