use std::convert::{TryFrom, TryInto};

use super::*;
use crate::data::ast::{Expr, ExprType};
use crate::data::lex::AssignmentToken;
use crate::data::prelude::*;

#[derive(Copy, Clone, Debug)]
#[rustfmt::skip]
enum Precedence {
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
    Ternary, // TODO: will this work with pratt parsing?
    Assignment(AssignmentToken),
}

impl Precedence {
    fn prec(&self) -> usize {
        use Precedence::*;
        match self {
            Mul | Div | Mod => 11,
            Add | Sub => 10,
            Shl | Shr => 9,
            Less | Greater | LessEq | GreaterEq => 8,
            Eq | Ne => 7,
            BitAnd => 6,
            BitXor => 5,
            BitOr => 4,
            LogAnd => 3,
            LogOr => 2,
            Ternary => 1, // TODO: will this work with pratt parsing?
            Assignment(_) => 0,
        }
    }
    fn left_associative(&self) -> bool {
        use Precedence::*;
        match self {
            Ternary | Assignment(_) => false,
            _ => true,
        }
    }
    fn constructor(&self) -> impl Fn(Expr, Expr) -> ExprType {
        use crate::data::lex::ComparisonToken;
        use ExprType::*;
        use Precedence::*;
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
            &Self::Assignment(token) => Box::new(move |a, b| Assign(a, b, token)),
            Self::Ternary => panic!("lol no"),
        };
        move |a, b| func(Box::new(a), Box::new(b))
    }
}

impl TryFrom<&Token> for Precedence {
    type Error = ();
    fn try_from(t: &Token) -> Result<Precedence, ()> {
        use crate::data::lex::ComparisonToken::{self as Compare, *};
        use Precedence::{self as Bin, *};
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
            _ => return Err(()),
        })
    }
}

impl<I: Iterator<Item = Lexeme>> Parser<I> {
    #[inline]
    pub fn expr(&mut self) -> SyntaxResult<Expr> {
        let start = self.unary_expr()?;
        self.binary_expr(start, 0)
    }
    // see `BinaryPrecedence` for all possible binary expressions
    fn binary_expr(&mut self, mut left: Expr, max_precedence: usize) -> SyntaxResult<Expr> {
        while let Some(binop) = self
            .peek_token()
            .and_then(|tok| Precedence::try_from(tok).ok())
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
            } else if let Precedence::Ternary = binop {
                // conditional_expression
                // : logical_or_expression
                // | logical_or_expression '?' expression ':' conditional_expression
                // ;
                let inner = self.expr()?;
                self.expect(Token::Colon)?;
                let right_start = self.unary_expr()?;
                let right = self.binary_expr(right_start, Precedence::Ternary.prec())?;

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
    fn unary_expr(&mut self) -> SyntaxResult<Expr> {
        let prefix = self.prefix_expr()?;
        self.postfix_expr(prefix)
    }

    // postfix_expression
    // : primary_expression
    // | postfix_expression '[' expression ']'
    // | postfix_expression '(' ')'
    // | postfix_expression '(' argument_expression_list ')'
    // | postfix_expression '.' IDENTIFIER
    // | postfix_expression PTR_OP IDENTIFIER
    // | postfix_expression INC_OP
    // | postfix_expression DEC_OP
    // ;
    fn postfix_expr(&mut self, mut expr: Expr) -> SyntaxResult<Expr> {
        // fortunately, they're all the same precedence
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

    // | '(' expr ')'
    // | unary_operator unary_expr
    // | "sizeof" '(' type_name ')'
    // | "sizeof" unary_expr
    // | "++" unary_expr
    // | "--" unary_expr
    // | ID
    // | LITERAL
    fn prefix_expr(&mut self) -> SyntaxResult<Expr> {
        if let Some(paren) = self.match_next(&Token::LeftParen) {
            let mut inner = self.expr()?;
            let end_loc = self.expect(Token::RightParen)?.location;
            inner.location = paren.location.merge(&end_loc);
            Ok(inner)
        } else if let Some(Locatable {
            data: constructor,
            location,
        }) = self.match_prefix_operator()
        {
            let inner = self.unary_expr()?;
            let location = location.merge(&inner.location);
            Ok(location.with(constructor(inner)))
        } else if let Some(loc) = self.match_id() {
            Ok(loc.map(ExprType::Id))
        } else if let Some(literal) = self.match_literal() {
            Ok(literal.map(ExprType::Literal))
        // TODO: cast expression, sizeof, ++, --
        // that will require distinguishing precedence for unary ops too
        } else {
            Err(self.next_location().with(SyntaxError::MissingPrimary))
        }
    }
    // '*' | '~' | '!' | '+' | '-' | '&'
    fn match_prefix_operator(&mut self) -> Option<Locatable<impl Fn(Expr) -> ExprType>> {
        // prefix operator
        let func = match self.peek_token()? {
            Token::Star => ExprType::Deref,
            Token::BinaryNot => ExprType::BitwiseNot,
            Token::LogicalNot => ExprType::LogicalNot,
            Token::Plus => ExprType::UnaryPlus,
            Token::Minus => ExprType::Negate,
            Token::Ampersand => ExprType::AddressOf,
            _ => return None,
        };
        let loc = self.next_token().unwrap().location;
        Some(Locatable::new(move |e| func(Box::new(e)), loc))
    }
    // '[' expr ']' | '(' argument* ')' | '.' ID | '->' ID | '++' | '--'
    fn match_postfix_op(&mut self) -> SyntaxResult<Option<Locatable<impl Fn(Expr) -> ExprType>>> {
        let next_location = |this: &mut Parser<_>| this.next_token().unwrap().location;
        let needs_id = |this: &mut Self, constructor: fn(Box<Expr>, InternedStr) -> ExprType| {
            let start = next_location(this);
            let Locatable { data: id, location } = this.expect_id()?;
            let location = start.merge(&location);
            Ok((Box::new(move |expr| constructor(expr, id)) as _, location))
        };
        // prefix operator
        let (func, location): (Box<dyn Fn(_) -> _>, _) = match self.peek_token() {
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
            _ => return Ok(None),
        };
        Ok(Some(Locatable {
            data: move |e| func(Box::new(e)),
            location,
        }))
    }
}

#[cfg(test)]
mod test {
    use crate::data::ast::{Expr, ExprType};
    use crate::test::*;
    use crate::SyntaxResult;
    use crate::*;

    fn assert_same(left: &str, right: &str) {
        assert_eq!(parse_all(left), parse_all(right))
    }

    fn assert_expr_display(left: &str, right: &str) {
        assert_eq!(expr(left).unwrap().to_string(), right);
    }

    fn expr(e: &str) -> SyntaxResult<Expr> {
        parser(e).expr()
    }

    #[test]
    fn parse_unary() {
        let expr_data = |s| expr(s).unwrap().data;
        let x = || Box::new(Location::default().with(ExprType::Id("x".into())));
        fn int() -> Box<Expr> {
            Box::new(Location::default().with(ExprType::Literal(Literal::Int(1))))
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
}
