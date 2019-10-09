use crate::backend::CHAR_BIT;
use crate::data::prelude::*;

macro_rules! fold_int_unary_op {
    ($($op: tt)*) => {
        |token| match token {
            Token::Int(i) => Token::Int($($op)*(i)),
            Token::UnsignedInt(u) => Token::UnsignedInt($($op)*(u)),
            Token::Char(c) => Token::Char($($op)*(c)),
            _ => token,
        }
    };
}

macro_rules! fold_int_bin_op {
    ($op: tt) => {
        |a: &Token, b: &Token, _| match (a, b) {
            (Token::Int(a), Token::Int(b)) => Some(Token::Int(a $op b)),
            (Token::UnsignedInt(a), Token::UnsignedInt(b)) => Some(Token::UnsignedInt(a $op b)),
            (Token::Char(a), Token::Char(b)) => Some(Token::Char(a $op b)),
            (_, _) => None,
        }
    }
}

macro_rules! fold_scalar_bin_op {
    ($op: tt) => {
        |a: &Token, b: &Token, _| match (a, b) {
            (Token::Int(a), Token::Int(b)) => Some(Token::Int(a $op b)),
            (Token::UnsignedInt(a), Token::UnsignedInt(b)) => Some(Token::UnsignedInt(a $op b)),
            (Token::Float(a), Token::Float(b)) => Some(Token::Float(a $op b)),
            (Token::Char(a), Token::Char(b)) => Some(Token::Char(a $op b)),
            // TODO: find a way to do this that allows `"hello" + 2 - 1`
            //(Token::Str(s), Token::Int(i)) | (Token::Int(i), Token::Str(s)) => {
            (_, _) => None,
        }
    }
}

macro_rules! fold_compare_op {
($left: expr, $right: expr, $constructor: ident, $op: tt, $compare: expr) => {{
        let (left, right) = ($left.const_fold()?, $right.const_fold()?);
        match (&left.expr, &right.expr) {
            (ExprType::Literal(a), ExprType::Literal(b)) => {
                match (a, b) {
                    (Token::Int(a), Token::Int(b)) => ExprType::Literal(Token::Int((a $op b) as i64)),
                    (Token::UnsignedInt(a), Token::UnsignedInt(b)) => ExprType::Literal(Token::Int((a $op b) as i64)),
                    #[allow(clippy::float_cmp)]
                    (Token::Float(a), Token::Float(b)) => ExprType::Literal(Token::Int((a $op b) as i64)),
                    (Token::Char(a), Token::Char(b)) => ExprType::Literal(Token::Int((a $op b) as i64)),
                    (_, _) => ExprType::$constructor(Box::new(left), Box::new(right), $compare),
                }
            }
            _ => ExprType::$constructor(Box::new(left), Box::new(right), $compare),
        }
    }}
}

impl Expr {
    pub fn is_zero(&self) -> bool {
        if let ExprType::Literal(token) = &self.expr {
            match *token {
                Token::Int(i) => i == 0,
                Token::UnsignedInt(u) => u == 0,
                Token::Float(f) => f == 0.0,
                Token::Char(c) => c == 0,
                _ => false,
            }
        } else {
            false
        }
    }
    pub fn is_negative(&self) -> bool {
        if let ExprType::Literal(token) = &self.expr {
            match *token {
                Token::Int(i) => i < 0,
                Token::Float(f) => f < 0.0,
                _ => false,
            }
        } else {
            false
        }
    }
    // first result: whether the expression itself is erroneous
    // second result: whether the expression was constexpr
    pub fn constexpr(self) -> SemanticResult<Result<Locatable<(Token, Type)>, Location>> {
        let folded = self.const_fold()?;
        let constexpr = match folded.expr {
            ExprType::Literal(token) => Ok(Locatable {
                data: (token, folded.ctype),
                location: folded.location,
            }),
            _ => Err(folded.location),
        };
        Ok(constexpr)
    }
    pub fn const_fold(self) -> SemanticResult<Expr> {
        let location = self.location;
        let folded = match self.expr {
            ExprType::Literal(_) => self.expr,
            ExprType::Id(ref name) => match &self.ctype {
                Type::Enum(_, members) => match members.iter().find(|member| member.0 == name.id) {
                    Some(enum_literal) => ExprType::Literal(Token::Int(enum_literal.1)),
                    _ => self.expr,
                },
                // TODO: if a variable were const, could we const fold Ids?
                _ => self.expr,
            },
            ExprType::Sizeof(ctype) => {
                let sizeof = ctype.sizeof().map_err(|data| Locatable {
                    data: data.into(),
                    location: location.clone(),
                })?;
                ExprType::Literal(Token::UnsignedInt(sizeof))
            }
            ExprType::Negate(expr) => expr.const_fold()?.map_literal(
                |token| match token {
                    Token::Int(i) => Token::Int(-i),
                    Token::UnsignedInt(u) => Token::UnsignedInt(0u64.wrapping_sub(u)),
                    Token::Char(c) => Token::Char(0u8.wrapping_sub(c)),
                    Token::Float(f) => Token::Float(-f),
                    _ => token,
                },
                ExprType::Negate,
            ),
            ExprType::LogicalNot(expr) => lnot_fold(expr.const_fold()?),
            ExprType::BitwiseNot(expr) => expr
                .const_fold()?
                .map_literal(fold_int_unary_op!(!), ExprType::BitwiseNot),
            ExprType::Comma(left, right) => {
                let (left, right) = (left.const_fold()?, right.const_fold()?);
                // check if we can ignore left or it has side effects
                if left.constexpr {
                    right.expr
                } else {
                    ExprType::Comma(Box::new(left), Box::new(right))
                }
            }
            ExprType::Noop(inner) => {
                let inner = inner.const_fold()?;
                ExprType::Noop(Box::new(inner))
            }
            ExprType::Deref(expr) => {
                let folded = expr.const_fold()?;
                if let ExprType::Literal(Token::Int(0)) = folded.expr {
                    return Err(Locatable {
                        data: "cannot dereference NULL pointer".into(),
                        location: folded.location,
                    });
                }
                ExprType::Deref(Box::new(folded))
            }
            ExprType::Add(left, right) => {
                left.literal_bin_op(*right, fold_scalar_bin_op!(+), ExprType::Add)?
            }
            ExprType::Sub(left, right) => left.literal_bin_op(
                *right,
                |a, b, ctype| match (a, b) {
                    (Token::Int(a), Token::Int(b)) => Some(Token::Int(a - b)),
                    (Token::UnsignedInt(a), Token::UnsignedInt(b)) => {
                        Some(Token::UnsignedInt(a.wrapping_sub(*b)))
                    }
                    #[allow(clippy::float_cmp)]
                    (Token::Float(a), Token::Float(b)) => Some(Token::Float(a - b)),
                    (Token::Char(a), Token::Char(b)) => {
                        if ctype.is_signed() {
                            Some(Token::Char(a - b))
                        } else {
                            Some(Token::Char(a.wrapping_sub(*b)))
                        }
                    }
                    (_, _) => None,
                },
                ExprType::Sub,
            )?,
            ExprType::Mul(left, right) => {
                left.literal_bin_op(*right, fold_scalar_bin_op!(*), ExprType::Mul)?
            }
            ExprType::Div(left, right) => {
                let right = right.const_fold()?;
                if right.is_zero() {
                    return Err(Locatable {
                        data: "cannot divide by zero".into(),
                        location,
                    });
                }
                left.literal_bin_op(right, fold_scalar_bin_op!(/), ExprType::Div)?
            }

            ExprType::Mod(left, right) => {
                let right = right.const_fold()?;
                if right.is_zero() {
                    return Err(Locatable {
                        data: "cannot take remainder of division by zero".into(),
                        location,
                    });
                }
                left.literal_bin_op(right, fold_int_bin_op!(%), ExprType::Mod)?
            }
            ExprType::Xor(left, right) => {
                left.literal_bin_op(*right, fold_int_bin_op!(^), ExprType::Xor)?
            }
            ExprType::BitwiseAnd(left, right) => {
                left.literal_bin_op(*right, fold_int_bin_op!(&), ExprType::BitwiseAnd)?
            }
            ExprType::BitwiseOr(left, right) => {
                left.literal_bin_op(*right, fold_int_bin_op!(|), ExprType::BitwiseOr)?
            }
            ExprType::Shift(left, right, true) => {
                shift_left(*left, *right, &self.ctype, &location)?
            }
            ExprType::Shift(left, right, false) => {
                shift_right(*left, *right, &self.ctype, &location)?
            }
            ExprType::Compare(left, right, Token::Less) => fold_compare_op!(left, right, Compare, <, Token::Less),
            ExprType::Compare(left, right, Token::LessEqual) => fold_compare_op!(left, right, Compare, <=, Token::LessEqual),
            ExprType::Compare(left, right, Token::Greater) => fold_compare_op!(left, right, Compare, >, Token::Greater),
            ExprType::Compare(left, right, Token::GreaterEqual) => fold_compare_op!(left, right, Compare, >=, Token::GreaterEqual),
            ExprType::Compare(left, right, Token::EqualEqual) => fold_compare_op!(left, right, Compare, ==, Token::EqualEqual),
            ExprType::Compare(left, right, Token::NotEqual) => fold_compare_op!(left, right, Compare, !=, Token::NotEqual),
            ExprType::Compare(_, _, _) => {
                unreachable!("only comparison tokens should appear in ExprType::Compare")
            }
            ExprType::Ternary(condition, then, otherwise) => {
                let (condition, then, otherwise) = (
                    condition.const_fold()?,
                    then.const_fold()?,
                    otherwise.const_fold()?,
                );
                match condition.expr {
                    ExprType::Literal(Token::Int(0)) => otherwise.expr,
                    ExprType::Literal(Token::Int(_)) => then.expr,
                    _ => {
                        ExprType::Ternary(Box::new(condition), Box::new(then), Box::new(otherwise))
                    }
                }
            }
            ExprType::FuncCall(func, params) => {
                let func = func.const_fold()?;
                #[rustfmt::skip]
                let params: Vec<Expr> = params
                    .into_iter()
                    .map(Self::const_fold)
                    .collect::<SemanticResult<_>>()?;
                // function calls are always non-constant
                // TODO: if we have access to the full source of a function, could we try to
                // TODO: fold across function boundaries?
                ExprType::FuncCall(Box::new(func), params)
            }
            ExprType::Member(expr, member) => {
                let expr = expr.const_fold()?;
                ExprType::Member(Box::new(expr), member)
            }
            ExprType::Assign(target, value, token) => {
                let (target, value) = (target.const_fold()?, value.const_fold()?);
                // TODO: could we propagate this information somehow?
                // e.g. fold `int main() { int x = 1; return x; }` to `return 1;`
                ExprType::Assign(Box::new(target), Box::new(value), token)
            }
            ExprType::PostIncrement(expr, increase) => {
                let expr = expr.const_fold()?;
                // this isn't constant for the same reason assignment isn't constant
                ExprType::PostIncrement(Box::new(expr), increase)
            }
            ExprType::Cast(expr) => cast(*expr, &self.ctype)?,
            ExprType::LogicalAnd(left, right) => {
                let left = cast(*left, &Type::Bool)?;
                if let ExprType::Literal(Token::Int(i)) = left {
                    if i == 0 {
                        ExprType::Literal(Token::Int(0))
                    } else {
                        cast(*right, &Type::Bool)?
                    }
                } else {
                    left
                }
            }
            ExprType::LogicalOr(left, right) => {
                let left = cast(*left, &Type::Bool)?;
                if let ExprType::Literal(Token::Int(i)) = left {
                    if i != 0 {
                        ExprType::Literal(Token::Int(1))
                    } else {
                        cast(*right, &Type::Bool)?
                    }
                } else {
                    left
                }
            }
            ExprType::StaticRef(inner) => ExprType::StaticRef(Box::new(inner.const_fold()?)),
        };
        let is_constexpr = match folded {
            ExprType::Literal(_) => true,
            _ => false,
        };
        //assert_eq!(self.constexpr, is_constexpr);
        Ok(Expr {
            expr: folded,
            constexpr: is_constexpr,
            location,
            ..self
        })
    }
    fn literal_bin_op<F, C>(
        self,
        other: Expr,
        fold_func: F,
        constructor: C,
    ) -> SemanticResult<ExprType>
    where
        F: FnOnce(&Token, &Token, &Type) -> Option<Token>,
        C: FnOnce(Box<Expr>, Box<Expr>) -> ExprType,
    {
        let (left, right) = (self.const_fold()?, other.const_fold()?);
        let literal = match (&left.expr, &right.expr) {
            (ExprType::Literal(left_token), ExprType::Literal(right_token)) => {
                fold_func(left_token, right_token, &left.ctype).map(ExprType::Literal)
            }
            _ => None,
        };
        Ok(literal.unwrap_or_else(|| constructor(Box::new(left), Box::new(right))))
    }
    fn map_literal<F, C>(self, literal_func: F, constructor: C) -> ExprType
    where
        F: FnOnce(Token) -> Token,
        C: FnOnce(Box<Expr>) -> ExprType,
    {
        match self.expr {
            ExprType::Literal(token) => ExprType::Literal(literal_func(token)),
            _ => constructor(Box::new(self)),
        }
    }
}

impl Token {
    fn non_negative_int(&self) -> Result<u64, ()> {
        match *self {
            Token::Int(i) if i >= 0 => Ok(i as u64),
            Token::UnsignedInt(u) => Ok(u),
            _ => Err(()),
        }
    }
}

fn cast(expr: Expr, ctype: &Type) -> SemanticResult<ExprType> {
    let expr = expr.const_fold()?;
    Ok(if let ExprType::Literal(ref token) = expr.expr {
        if let Some(token) = const_cast(token, ctype) {
            ExprType::Literal(token)
        } else {
            ExprType::Cast(Box::new(expr))
        }
    } else {
        ExprType::Cast(Box::new(expr))
    })
}

/// since we only have Int and Float for literals,
/// all this does is make sure the folded value is in a valid range
/// TODO: when we add suffix literals, that will have type information
/// and we can use that to store the new type
fn const_cast(token: &Token, ctype: &Type) -> Option<Token> {
    let token = match (token, ctype) {
        (Token::Int(i), Type::Bool) => Token::Int((*i != 0) as i64),
        (Token::Int(i), Type::Double) | (Token::Int(i), Type::Float) => Token::Float(*i as f64),
        (Token::Int(i), ty) if ty.is_integral() && ty.is_signed() => Token::Int(*i),
        (Token::Int(i), ty) if ty.is_integral() => Token::UnsignedInt(*i as u64),
        (Token::UnsignedInt(u), Type::Bool) => Token::Int((*u != 0) as i64),
        (Token::UnsignedInt(u), Type::Double) | (Token::UnsignedInt(u), Type::Float) => {
            Token::Float(*u as f64)
        }
        (Token::UnsignedInt(u), ty) if ty.is_integral() && ty.is_signed() => Token::Int(*u as i64),
        (Token::UnsignedInt(u), ty) if ty.is_integral() => Token::UnsignedInt(*u),
        (Token::Float(f), Type::Bool) => Token::Int((*f != 0.0) as i64),
        (Token::Float(f), Type::Double) | (Token::Float(f), Type::Float) => Token::Float(*f),
        (Token::Float(f), ty) if ty.is_integral() && ty.is_signed() => Token::Int(*f as i64),
        (Token::Float(f), ty) if ty.is_integral() => Token::UnsignedInt(*f as u64),
        _ => return None,
    };
    Some(token)
}

fn lnot_fold(expr: Expr) -> ExprType {
    match expr.expr {
        ExprType::Literal(Token::Int(i)) => ExprType::Literal(Token::Int((i == 0) as i64)),
        ExprType::Literal(Token::Float(f)) => ExprType::Literal(Token::Int((f == 0.0) as i64)),
        ExprType::Literal(Token::Char(c)) => ExprType::Literal(Token::Int((c == 0) as i64)),
        ExprType::Literal(Token::Str(_)) => ExprType::Literal(Token::Int(0)),
        _ => ExprType::LogicalNot(Box::new(expr)),
    }
}

fn shift_right(
    left: Expr,
    right: Expr,
    ctype: &Type,
    location: &Location,
) -> SemanticResult<ExprType> {
    let (left, right) = (left.const_fold()?, right.const_fold()?);
    if let ExprType::Literal(token) = right.expr {
        let shift = match token.non_negative_int() {
            Ok(u) => u,
            Err(_) => err!(
                "cannot shift left by a negative amount".into(),
                location.clone()
            ),
        };
        let sizeof = ctype.sizeof().map_err(|err| Locatable {
            data: err.into(),
            location: location.clone(),
        })?;
        // Rust panics if the shift is greater than the size of the type
        if shift >= sizeof {
            return Ok(ExprType::Literal(if ctype.is_signed() {
                Token::Int(0)
            } else {
                Token::UnsignedInt(0)
            }));
        }
        if let ExprType::Literal(token) = left.expr {
            Ok(match token {
                Token::Int(i) => ExprType::Literal(Token::Int(i.wrapping_shr(shift as u32))),
                Token::UnsignedInt(u) => {
                    ExprType::Literal(Token::UnsignedInt(u.wrapping_shr(shift as u32)))
                }
                _ => unreachable!("only ints and unsigned ints can be right shifted"),
            })
        } else {
            Ok(ExprType::Shift(
                Box::new(left),
                Box::new(Expr {
                    expr: ExprType::Literal(token),
                    ..right
                }),
                false,
            ))
        }
    } else {
        Ok(ExprType::Shift(Box::new(left), Box::new(right), false))
    }
}

fn shift_left(
    left: Expr,
    right: Expr,
    ctype: &Type,
    location: &Location,
) -> SemanticResult<ExprType> {
    let (left, right) = (left.const_fold()?, right.const_fold()?);
    if let ExprType::Literal(token) = right.expr {
        let shift = match token.non_negative_int() {
            Ok(u) => u,
            Err(_) => err!(
                "cannot shift left by a negative amount".into(),
                location.clone()
            ),
        };
        if left.ctype.is_signed() {
            let size = match left.ctype.sizeof() {
                Ok(s) => s,
                Err(err) => err!(err.into(), location.clone()),
            };
            let max_shift = u64::from(CHAR_BIT) * size;
            if shift >= max_shift {
                err!(
                    format!(
                        "cannot shift left by {} or more bits for type '{}' (got {})",
                        max_shift, ctype, shift
                    ),
                    location.clone(),
                );
            }
        }
        Ok(match left.expr {
            ExprType::Literal(Token::Int(i)) => {
                let (result, overflow) = i.overflowing_shl(shift as u32);
                if overflow {
                    err!(
                        "overflow in shift left during constant folding".into(),
                        location.clone()
                    );
                }
                ExprType::Literal(Token::Int(result))
            }
            ExprType::Literal(Token::UnsignedInt(u)) => {
                ExprType::Literal(Token::UnsignedInt(u.wrapping_shl(shift as u32)))
            }
            _ => ExprType::Shift(
                Box::new(left),
                Box::new(Expr {
                    expr: ExprType::Literal(token),
                    ..right
                }),
                false,
            ),
        })
    } else {
        Ok(ExprType::Shift(Box::new(left), Box::new(right), false))
    }
}
