use std::convert::TryFrom;

use super::*;
use crate::data::ast::{Expr, ExprType, TypeName};
use crate::data::lex::{AssignmentToken, Keyword};
use crate::data::*;

trait UnaryExprFn: FnOnce(Expr) -> ExprType {}
impl<T: FnOnce(Expr) -> ExprType> UnaryExprFn for T {}

#[derive(Copy, Clone, Debug)]
#[rustfmt::skip]
enum BinaryPrecedence {
    Mul, Div, Mod,
    Add, Sub,
    Shl, Shr,
    Less, Greater, LessEq, GreaterEq,
    Eq, Ne,
    BitAnd,
    BitXor,
    BitOr,
    LogAnd,
    LogOr,
    Ternary,
    Assignment(AssignmentToken),
    Comma,
}

impl BinaryPrecedence {
    fn prec(self) -> usize {
        use BinaryPrecedence::*;
        match self {
            Mul | Div | Mod => 12,
            Add | Sub => 11,
            Shl | Shr => 10,
            Less | Greater | LessEq | GreaterEq => 9,
            Eq | Ne => 8,
            BitAnd => 7,
            BitXor => 6,
            BitOr => 5,
            LogAnd => 4,
            LogOr => 3,
            Ternary => 2,
            Assignment(_) => 1,
            Comma => 0,
        }
    }
    fn left_associative(self) -> bool {
        use BinaryPrecedence::*;
        match self {
            Ternary | Assignment(_) => false,
            _ => true,
        }
    }
    fn constructor(self) -> impl Fn(Expr, Expr) -> ExprType {
        use crate::data::lex::ComparisonToken;
        use BinaryPrecedence::*;
        use ExprType::*;
        let func: Box<dyn Fn(_, _) -> _> = match self {
            Self::Mul => Box::new(ExprType::Mul),
            Self::Div => Box::new(ExprType::Div),
            Self::Mod => Box::new(ExprType::Mod),
            Self::Add => Box::new(ExprType::Add),
            Self::Sub => Box::new(ExprType::Sub),
            Shl => Box::new(|a, b| Shift(a, b, true)),
            Shr => Box::new(|a, b| Shift(a, b, false)),
            Less => Box::new(|a, b| Compare(a, b, ComparisonToken::Less)),
            Greater => Box::new(|a, b| Compare(a, b, ComparisonToken::Greater)),
            LessEq => Box::new(|a, b| Compare(a, b, ComparisonToken::LessEqual)),
            GreaterEq => Box::new(|a, b| Compare(a, b, ComparisonToken::GreaterEqual)),
            Eq => Box::new(|a, b| Compare(a, b, ComparisonToken::EqualEqual)),
            Ne => Box::new(|a, b| Compare(a, b, ComparisonToken::NotEqual)),
            BitAnd => Box::new(BitwiseAnd),
            BitXor => Box::new(Xor),
            BitOr => Box::new(BitwiseOr),
            LogAnd => Box::new(LogicalAnd),
            LogOr => Box::new(LogicalOr),
            Self::Assignment(token) => Box::new(move |a, b| Assign(a, b, token)),
            Self::Ternary => panic!("lol no"),
            Self::Comma => Box::new(ExprType::Comma),
        };
        move |a, b| func(Box::new(a), Box::new(b))
    }
}

impl TryFrom<&Token> for BinaryPrecedence {
    type Error = ();
    fn try_from(t: &Token) -> Result<BinaryPrecedence, ()> {
        use crate::data::lex::ComparisonToken as Compare;
        use BinaryPrecedence::{self as Bin, *};
        use Token::*;
        Ok(match t {
            Star => Bin::Mul,
            Divide => Div,
            Token::Mod => Bin::Mod,
            Plus => Add,
            Minus => Sub,
            ShiftLeft => Shl,
            ShiftRight => Shr,
            Comparison(Compare::Less) => Bin::Less,
            Comparison(Compare::Greater) => Bin::Greater,
            Comparison(Compare::LessEqual) => Bin::LessEq,
            Comparison(Compare::GreaterEqual) => Bin::GreaterEq,
            Comparison(Compare::EqualEqual) => Bin::Eq,
            Comparison(Compare::NotEqual) => Bin::Ne,
            Ampersand => BitAnd,
            Xor => BitXor,
            BitwiseOr => BitOr,
            LogicalAnd => LogAnd,
            LogicalOr => LogOr,
            Token::Assignment(x) => Bin::Assignment(*x),
            Question => Ternary,
            Token::Comma => Bin::Comma,
            _ => return Err(()),
        })
    }
}

impl<I: Lexer> Parser<I> {
    #[inline]
    pub fn expr(&mut self) -> SyntaxResult<Expr> {
        let start = self.unary_expr()?;
        self.binary_expr(start, 0)
    }
    #[inline]
    pub fn assignment_expr(&mut self) -> SyntaxResult<Expr> {
        self.custom_expr(BinaryPrecedence::Assignment(AssignmentToken::Equal))
    }
    #[inline]
    pub fn ternary_expr(&mut self) -> SyntaxResult<Expr> {
        self.custom_expr(BinaryPrecedence::Ternary)
    }
    fn custom_expr(&mut self, prec: BinaryPrecedence) -> SyntaxResult<Expr> {
        let start = self.unary_expr()?;
        self.binary_expr(start, prec.prec())
    }
    // see `BinaryPrecedence` for all possible binary expressions
    fn binary_expr(&mut self, mut left: Expr, max_precedence: usize) -> SyntaxResult<Expr> {
        let _guard = self.recursion_check();
        while let Some(binop) = self
            .peek_token()
            .and_then(|tok| BinaryPrecedence::try_from(tok).ok())
        {
            let prec = binop.prec();
            if prec < max_precedence {
                break;
            }
            self.next_token();
            let location = left.location;
            let right = if binop.left_associative() {
                let inner_left = self.unary_expr()?;
                self.binary_expr(inner_left, prec + 1)?
            } else if let BinaryPrecedence::Ternary = binop {
                // conditional_expression
                // : logical_or_expression
                // | logical_or_expression '?' expression ':' conditional_expression
                // ;
                // <http://www.quut.com/c/ANSI-C-grammar-y.html#conditional_expression>
                let inner = self.expr()?;
                self.expect(Token::Colon)?;
                let right_start = self.unary_expr()?;
                let right = self.binary_expr(right_start, BinaryPrecedence::Ternary.prec())?;

                let location = left.location.merge(&inner.location).merge(&right.location);
                let ternary = ExprType::Ternary(Box::new(left), Box::new(inner), Box::new(right));
                left = Expr::new(ternary, location);
                continue;
            } else {
                let inner_left = self.unary_expr()?;
                self.binary_expr(inner_left, prec)?
            };

            let constructor = binop.constructor();
            let location = location.merge(&right.location);
            left = location.with(constructor(left, right));
        }
        Ok(left)
    }
    // ambiguity between '(' expr ')' and '(' type_name ')'
    // NOTE: there is no distinction between EOF and a non-parenthesized type here
    fn parenthesized_type(&mut self) -> SyntaxResult<Option<Locatable<TypeName>>> {
        if self.peek_token() == Some(&Token::LeftParen) {
            if let Some(lookahead) = self.peek_next_token() {
                if lookahead.is_decl_specifier() {
                    let left_paren = self.next_token().unwrap().location;
                    let (mut ctype, saw_paren) = self.type_name(&[&Token::RightParen])?;
                    let right_paren = if let Some(token) = saw_paren {
                        token.location
                    } else {
                        self.expect(Token::RightParen)?.location
                    };
                    ctype.location = left_paren.merge(right_paren);
                    return Ok(Some(ctype));
                }
            }
        }
        Ok(None)
    }
    // prefix_operator* postfix_expr
    //
    // this takes the place of `unary_expr` in the yacc grammar
    fn unary_expr(&mut self) -> SyntaxResult<Expr> {
        // prefix expressions
        let mut prefixes = Vec::new();
        // hack: `sizeof` can be either a unary or primary expression, so we special-case it
        let mut inner = loop {
            if let Some(Locatable {
                data: constructor,
                location,
            }) = self.match_prefix_operator()
            {
                prefixes.push((constructor, location));
            // these keywords can be followed by either a type name or an expression
            } else if let Some(keyword) = self.match_keywords(&[Keyword::Sizeof, Keyword::Alignof])
            {
                // `sizeof(int)` is a primary expr
                if let Some(mut ctype) = self.parenthesized_type()? {
                    ctype.location = keyword.location.merge(ctype.location);
                    let constructor = if keyword.data == Keyword::Sizeof {
                        ExprType::SizeofType
                    } else {
                        ExprType::AlignofType
                    };
                    // short-circuit here
                    break self.postfix_expr(ctype.map(constructor))?;
                // `sizeof +1` is a unary expr
                } else {
                    let constructor = if keyword.data == Keyword::Sizeof {
                        ExprType::SizeofExpr
                    } else {
                        ExprType::AlignofExpr
                    };
                    prefixes.push((
                        Box::new(move |a| constructor(Box::new(a))),
                        keyword.location,
                    ));
                }
            } else {
                break self.primary_expr()?;
            }
        };
        while let Some((constructor, location)) = prefixes.pop() {
            inner = Locatable::new(constructor(inner), location);
        }
        Ok(inner)
    }
    // postfix_expression: primary_expression postfix_op*
    // primary_expression: '(' expr ')' | 'sizeof' unary_expression | 'alignof' unary_expression | ID | LITERAL
    // <http://www.quut.com/c/ANSI-C-grammar-y.html#postfix_expression>
    //
    // TODO: `sizeof` and `alignof` should be unary expressions, not primary expressions
    #[inline]
    fn primary_expr(&mut self) -> SyntaxResult<Expr> {
        // primary expression
        // this must be an expression since we already consumed all the prefix expressions
        let primary = if let Some(paren) = self.match_next(&Token::LeftParen) {
            // take out lots of guards since there's a lot of indirection
            let _guard = self.recursion_check();
            let _guard2 = self.recursion_check();
            let mut inner = self.expr()?;
            let end_loc = self.expect(Token::RightParen)?.location;
            inner.location = paren.location.merge(&end_loc);
            inner
        } else if let Some(loc) = self.match_id() {
            loc.map(ExprType::Id)
        } else if let Some(literal) = self.match_literal() {
            let loc = literal.location;
            match literal.data.parse() {
                Ok(literal) => loc.with(literal).map(ExprType::Literal),
                Err(err) => return Err(loc.with(err)),
            }
        } else {
            return Err(self.next_location().with(SyntaxError::MissingPrimary));
        };
        self.postfix_expr(primary)
    }

    // `expr` should be a primary expression
    fn postfix_expr(&mut self, mut expr: Expr) -> SyntaxResult<Expr> {
        // fortunately, all postfix expressions have the same precedence
        while let Some(Locatable {
            data: postfix_op,
            location,
        }) = self.match_postfix_op()?
        {
            let location = expr.location.merge(&location);
            expr = location.with(postfix_op(expr));
        }
        Ok(expr)
    }

    // '(' TYPE_NAME ')' | '*' | '~' | '!' | '+' | '-' | '&' | '++' | '--'
    fn match_prefix_operator(&mut self) -> Option<Locatable<Box<dyn UnaryExprFn>>> {
        let maybe_type = self.parenthesized_type().unwrap_or_else(|err| {
            self.error_handler.push_back(err);
            None
        });
        if let Some(cast) = maybe_type {
            let loc = cast.location;
            return Some(Locatable::new(
                Box::new(move |expr| ExprType::Cast(cast.data, Box::new(expr))),
                loc,
            ));
        }
        // prefix operator
        let func = match self.peek_token()? {
            Token::Star => ExprType::Deref,
            Token::BinaryNot => ExprType::BitwiseNot,
            Token::LogicalNot => ExprType::LogicalNot,
            Token::Plus => ExprType::UnaryPlus,
            Token::Minus => ExprType::Negate,
            Token::Ampersand => ExprType::AddressOf,
            Token::PlusPlus => |e| ExprType::PreIncrement(e, true),
            Token::MinusMinus => |e| ExprType::PreIncrement(e, false),
            _ => return None,
        };
        let loc = self.next_token().unwrap().location;
        Some(Locatable::new(Box::new(move |e| func(Box::new(e))), loc))
    }
    // '[' expr ']' | '(' argument* ')' | '.' ID | '->' ID | '++' | '--'
    fn match_postfix_op(&mut self) -> SyntaxResult<Option<Locatable<impl UnaryExprFn>>> {
        let next_location = |this: &mut Parser<_>| this.next_token().unwrap().location;
        let needs_id = |this: &mut Self, constructor: fn(Box<Expr>, InternedStr) -> ExprType| {
            let start = next_location(this);
            let Locatable { data: id, location } = this.expect_id()?;
            let location = start.merge(&location);
            Ok((Box::new(move |expr| constructor(expr, id)) as _, location))
        };
        // postfix operator
        let (func, location): (Box<dyn FnOnce(_) -> _>, _) = match self.peek_token() {
            Some(Token::Dot) => needs_id(self, ExprType::Member)?,
            Some(Token::StructDeref) => needs_id(self, ExprType::DerefMember)?,
            Some(Token::PlusPlus) => (
                Box::new(|expr| ExprType::PostIncrement(expr, true)) as _,
                next_location(self),
            ),
            Some(Token::MinusMinus) => (
                Box::new(|expr| ExprType::PostIncrement(expr, false)) as _,
                next_location(self),
            ),
            Some(Token::LeftBracket) => {
                let start = next_location(self);
                let index = self.expr()?;
                let end = self.expect(Token::RightBracket)?.location;
                let location = start.merge(&index.location).merge(&end);
                (
                    Box::new(move |expr| ExprType::Index(expr, Box::new(index))),
                    location,
                )
            }
            Some(Token::LeftParen) => {
                let mut start = next_location(self);
                let mut args = Vec::new();
                if let Some(token) = self.match_next(&Token::RightParen) {
                    start = start.merge(&token.location);
                } else {
                    loop {
                        // TODO: maybe we could do some error handling here and consume the end right paren
                        let arg = self.ternary_expr()?;
                        start.merge(&arg.location);
                        args.push(arg);
                        if let Some(token) = self.match_next(&Token::Comma) {
                            start.merge(token.location);
                        } else {
                            let token = self.expect(Token::RightParen)?;
                            start = start.merge(token.location);
                            break;
                        }
                    }
                };
                (Box::new(move |expr| ExprType::FuncCall(expr, args)), start)
            }
            _ => return Ok(None),
        };
        Ok(Some(Locatable {
            data: move |e| func(Box::new(e)),
            location,
        }))
    }
}

#[cfg(test)]
pub(crate) mod test {
    use super::SyntaxResult;
    use crate::data::ast::{Expr, ExprType};
    use crate::parse::test::*;
    use crate::parse::*;

    fn assert_same(left: &str, right: &str) {
        assert_eq!(
            expr(left).unwrap().to_string(),
            expr(right).unwrap().to_string()
        );
    }
    fn assert_expr_display(left: &str, right: &str) {
        assert_eq!(expr(left).unwrap().to_string(), right);
    }

    pub(crate) fn expr(e: &str) -> SyntaxResult<Expr> {
        parser(e).expr()
    }

    #[test]
    fn parse_prefix() {
        let expr_data = |s| expr(s).unwrap().data;
        let x = || Box::new(Location::default().with(ExprType::Id("x".into())));
        fn int() -> Box<Expr> {
            Box::new(Location::default().with(ExprType::Literal(LiteralValue::Int(1))))
        }
        fn assert_unary_int(s: &str, c: impl Fn(Box<Expr>) -> ExprType) {
            assert_eq!(expr(s).unwrap().data, c(int()));
        }
        assert_unary_int("1", |i| i.data);
        assert_unary_int("(((((1)))))", |i| i.data);
        assert_unary_int("+(1)", ExprType::UnaryPlus);
        assert_unary_int("-((1))", ExprType::Negate);
        assert_unary_int("*1", ExprType::Deref);
        assert_unary_int("~1", ExprType::BitwiseNot);
        assert_unary_int("!1", ExprType::LogicalNot);
        assert_unary_int("&1", ExprType::AddressOf);

        assert_eq!(expr_data("x"), x().data);
        assert_eq!(expr_data("x"), x().data);
        assert_eq!(expr_data("(((((x)))))"), x().data);
        assert_eq!(expr_data("+(x)"), ExprType::UnaryPlus(x()));
        assert_eq!(expr_data("-((x))"), ExprType::Negate(x()));
        assert_eq!(expr_data("*x"), ExprType::Deref(x()));
        assert_eq!(expr_data("~x"), ExprType::BitwiseNot(x()));
        assert_eq!(expr_data("!x"), ExprType::LogicalNot(x()));
        assert_eq!(expr_data("&x"), ExprType::AddressOf(x()));

        assert_same("++A[1]", "++(A[1])");
        assert_same("A[1] += 1", "(A[1]) += 1");
    }
    #[test]
    fn parse_postfix() {
        assert_expr_display("a[1]", "(a)[1]");
        assert_expr_display("a++", "(a)++");
        assert_expr_display("a--", "(a)--");
        assert_expr_display("a--", "(a)--");
        assert_expr_display("a++--->b.c[d]", "(((((a)++)--)->b).c)[d]");
        assert_expr_display("a(1, 2)(3)(4+5)", "(((a)(1, 2))(3))((4) + (5))");
        // lol why not
        assert_expr_display("1()()()", "(((1)())())()");
    }
    #[test]
    fn parse_binary() {
        assert_eq!(
            expr("1 = 2 = 3 + 4*5 + 6 + 7").unwrap().to_string(),
            "(1) = ((2) = ((((3) + ((4) * (5))) + (6)) + (7)))"
        );
    }
    #[test]
    fn parse_ternary() {
        assert_expr_display("1||2 ? 3||4 : 5", "((1) || (2)) ? ((3) || (4)) : (5)");
        assert_expr_display("1||2 ? 3?4:5 : 6", "((1) || (2)) ? ((3) ? (4) : (5)) : (6)");
    }
    #[test]
    fn parse_casts() {
        assert_expr_display(
            "(int)(char)(double)(_Bool)0",
            "(int)((char)((double)((_Bool)(0))))",
        );
        assert_expr_display("(int)&(char)0", "(int)(&((char)(0)))");
        assert_expr_display("sizeof 1 + 2", "(sizeof(1)) + (2)");
        // sizeof(int) takes precedence over (int)1
        assert_expr_display("sizeof (int)1 + 2", "sizeof(int)");
    }
    #[test]
    fn sizeof() {
        assert_same("sizeof(int)++", "(sizeof(int))++");
        assert_same("++sizeof(int)", "++(sizeof(int))");
    }
}
