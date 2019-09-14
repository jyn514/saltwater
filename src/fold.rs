use crate::backend::CHAR_BIT;
use crate::data::prelude::*;

macro_rules! fold_int_bin_op {
    ($left: expr, $right: expr, $constructor: expr, $types: expr, $op: tt) => {{
        let (left, right) = ($left.const_fold($types)?, $right.const_fold($types)?);
        match (&left.expr, &right.expr) {
            (ExprType::Literal(a), ExprType::Literal(b)) => {
                match (a, b) {
                    (Token::Int(a), Token::Int(b)) => ExprType::Literal(Token::Int(a $op b)),
                    (Token::UnsignedInt(a), Token::UnsignedInt(b)) => ExprType::Literal(Token::UnsignedInt(a $op b)),
                    (Token::Char(a), Token::Char(b)) => ExprType::Literal(Token::Char(a $op b)),
                    (_, _) => $constructor(Box::new(left), Box::new(right)),
                }
            }
            _ => $constructor(Box::new(left), Box::new(right)),
        }
    }}
}

macro_rules! fold_scalar_bin_op {
    ($left: expr, $right: expr, $constructor: ident, $types: expr, $op: tt) => {{
        let (left, right) = ($left.const_fold($types)?, $right.const_fold($types)?);
        match (&left.expr, &right.expr) {
            (ExprType::Literal(a), ExprType::Literal(b)) => {
                match (a, b) {
                    (Token::Int(a), Token::Int(b)) => ExprType::Literal(Token::Int(a $op b)),
                    (Token::UnsignedInt(a), Token::UnsignedInt(b)) => ExprType::Literal(Token::UnsignedInt(a $op b)),
                    (Token::Float(a), Token::Float(b)) => ExprType::Literal(Token::Float(a $op b)),
                    (Token::Char(a), Token::Char(b)) => ExprType::Literal(Token::Char(a $op b)),
                    // TODO: find a way to do this that allows `"hello" + 2 - 1`
                    //(Token::Str(s), Token::Int(i)) | (Token::Int(i), Token::Str(s)) => {
                    (_, _) => ExprType::$constructor(Box::new(left), Box::new(right)),
                }
            }
            _ => ExprType::$constructor(Box::new(left), Box::new(right)),
        }
    }}
}

/*
fn fold_compare_op<C, F>(
    left: Expr,
    right: Expr,
    constructor: C,
    op: F,
    compare: Token,
) -> SemanticResult<ExprType>
where
    C: Fn(Box<Expr>, Box<Expr>) -> ExprType,
    F: Fn(T, T) -> bool,
    T: PartialEq + Ord,
{
    let (left, right) = (left.const_fold()?, right.const_fold()?);
    match (&left.expr, &right.expr) {
        (ExprType::Literal(a), ExprType::Literal(b)) => {
            match (a, b) {
                (Token::Int(a), Token::Int(b)) => ExprType::Literal(Token::Int(op(a, b) as i64)),
                (Token::Float(a), Token::Float(b)) => {
                    ExprType::Literal(Token::Float(op(a, b) as f64))
                }
                (Token::Char(a), Token::Char(b)) => ExprType::Literal(Token::Char(op(a, b) as u8)),
                // TODO: find a way to do this that allows `"hello" + 2 - 1`
                //(Token::Str(s), Token::Int(i)) | (Token::Int(i), Token::Str(s)) => {
                (_, _) => constructor(Box::new(left), Box::new(right)),
            }
        }
        _ => constructor(Box::new(left), Box::new(right)),
    }
}
*/

macro_rules! fold_compare_op {
($left: expr, $right: expr, $constructor: ident, $op: tt, $compare: expr, $types: expr) => {{
        let (left, right) = ($left.const_fold($types)?, $right.const_fold($types)?);
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
    pub fn constexpr(
        self,
        types: &Types,
    ) -> SemanticResult<Result<Locatable<(Token, Type)>, Location>> {
        let folded = self.const_fold(types)?;
        let constexpr = match folded.expr {
            ExprType::Literal(token) => Ok(Locatable {
                data: (token, types[folded.ctype]),
                location: folded.location,
            }),
            _ => Err(folded.location),
        };
        Ok(constexpr)
    }
    pub fn const_fold(self, types: &Types) -> SemanticResult<Expr> {
        let location = self.location;
        let folded = match self.expr {
            ExprType::Literal(_) => self.expr,
            // TODO: if a variable were const, could we const fold Ids?
            ExprType::Id(_) => self.expr,
            ExprType::Sizeof(ctype) => {
                let sizeof = types[ctype].sizeof(types).map_err(|data| Locatable {
                    data: data.into(),
                    location: location.clone(),
                })?;
                ExprType::Literal(Token::UnsignedInt(sizeof))
            }
            ExprType::Negate(expr) => {
                let expr = expr.const_fold(types)?;
                match expr.expr {
                    ExprType::Literal(Token::Int(i)) => ExprType::Literal(Token::Int(-i)),
                    ExprType::Literal(Token::Float(f)) => ExprType::Literal(Token::Float(-f)),
                    _ => ExprType::Negate(Box::new(expr)),
                }
            }
            ExprType::LogicalNot(expr) => lnot_fold(expr.const_fold(types)?),
            ExprType::BitwiseNot(expr) => {
                let expr = expr.const_fold(types)?;
                match expr.expr {
                    ExprType::Literal(Token::Int(i)) => ExprType::Literal(Token::Int(!i)),
                    _ => ExprType::BitwiseNot(Box::new(expr)),
                }
            }
            ExprType::Comma(left, right) => {
                let (left, right) = (left.const_fold(types)?, right.const_fold(types)?);
                // check if we can ignore left or it has side effects
                if left.constexpr {
                    right.expr
                } else {
                    ExprType::Comma(Box::new(left), Box::new(right))
                }
            }
            ExprType::Deref(expr) => {
                let folded = expr.const_fold(types)?;
                if let ExprType::Literal(Token::Int(0)) = folded.expr {
                    return Err(Locatable {
                        data: "cannot dereference NULL pointer".into(),
                        location: folded.location,
                    });
                }
                ExprType::Deref(Box::new(folded))
            }
            ExprType::Add(left, right) => fold_scalar_bin_op!(left, right, Add, types, +),
            ExprType::Sub(left, right) => fold_scalar_bin_op!(left, right, Sub, types, -),
            ExprType::Mul(left, right) => fold_scalar_bin_op!(left, right, Mul, types, *),
            ExprType::Div(left, right) => {
                let right = right.const_fold(types)?;
                if right.is_zero() {
                    return Err(Locatable {
                        data: "cannot divide by zero".into(),
                        location,
                    });
                }
                fold_scalar_bin_op!(left, right, Div, types, /)
            }

            ExprType::Mod(left, right) => {
                let right = right.const_fold(types)?;
                if right.is_zero() {
                    return Err(Locatable {
                        data: "cannot take remainder of division by zero".into(),
                        location,
                    });
                }
                fold_int_bin_op!(left, right, ExprType::Mod, types, %)
            }
            ExprType::Xor(left, right) => fold_int_bin_op!(left, right, ExprType::Xor, types, ^),
            ExprType::BitwiseAnd(left, right) => {
                fold_int_bin_op!(left, right, ExprType::BitwiseAnd, types, &)
            }
            ExprType::BitwiseOr(left, right) => {
                fold_int_bin_op!(left, right, ExprType::BitwiseOr, types, |)
            }
            ExprType::Shift(left, right, true) => {
                shift_left(*left, *right, &types[self.ctype], types, &location)?
            }
            ExprType::Shift(left, right, false) => {
                shift_right(*left, *right, &types[self.ctype], types, &location)?
            }
            ExprType::Compare(left, right, Token::Less) => {
                fold_compare_op!(left, right, Compare, <, Token::Less, types)
            }
            ExprType::Compare(left, right, Token::LessEqual) => {
                fold_compare_op!(left, right, Compare, <=, Token::LessEqual, types)
            }
            ExprType::Compare(left, right, Token::Greater) => {
                fold_compare_op!(left, right, Compare, >, Token::Greater, types)
            }
            ExprType::Compare(left, right, Token::GreaterEqual) => {
                fold_compare_op!(left, right, Compare, >=, Token::GreaterEqual, types)
            }
            ExprType::Compare(left, right, Token::EqualEqual) => {
                fold_compare_op!(left, right, Compare, ==, Token::EqualEqual, types)
            }
            ExprType::Compare(left, right, Token::NotEqual) => {
                fold_compare_op!(left, right, Compare, !=, Token::NotEqual, types)
            }
            ExprType::Compare(_, _, _) => {
                unreachable!("only comparison tokens should appear in ExprType::Compare")
            }
            ExprType::Ternary(condition, then, otherwise) => {
                let (condition, then, otherwise) = (
                    condition.const_fold(types)?,
                    then.const_fold(types)?,
                    otherwise.const_fold(types)?,
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
                let func = func.const_fold(types)?;
                #[rustfmt::skip]
                let params: Vec<Expr> = params
                    .into_iter()
                    .map(|param| param.const_fold(types))
                    .collect::<SemanticResult<_>>()?;
                // function calls are always non-constant
                // TODO: if we have access to the full source of a function, could we try to
                // TODO: fold across function boundaries?
                ExprType::FuncCall(Box::new(func), params)
            }
            ExprType::Member(expr, member) => {
                let expr = expr.const_fold(types)?;
                ExprType::Member(Box::new(expr), member)
            }
            ExprType::Assign(target, value, token) => {
                let (target, value) = (target.const_fold(types)?, value.const_fold(types)?);
                // TODO: could we propagate this information somehow?
                // e.g. fold `int main() { int x = 1; return x; }` to `return 1;`
                ExprType::Assign(Box::new(target), Box::new(value), token)
            }
            ExprType::Increment(expr, pre, post) => {
                let expr = expr.const_fold(types)?;
                // this isn't constant for the same reason assignment isn't constant
                ExprType::Increment(Box::new(expr), pre, post)
            }
            ExprType::Cast(expr) => cast(*expr, &types[self.ctype], types)?,
            ExprType::LogicalAnd(left, right) => {
                let left = cast(*left, &Type::Bool, types)?;
                if let ExprType::Literal(Token::Int(i)) = left {
                    if i == 0 {
                        ExprType::Literal(Token::Int(0))
                    } else {
                        cast(*right, &Type::Bool, types)?
                    }
                } else {
                    left
                }
            }
            ExprType::LogicalOr(left, right) => {
                let left = cast(*left, &Type::Bool, types)?;
                if let ExprType::Literal(Token::Int(i)) = left {
                    if i != 0 {
                        ExprType::Literal(Token::Int(1))
                    } else {
                        cast(*right, &Type::Bool, types)?
                    }
                } else {
                    left
                }
            }
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

fn cast(expr: Expr, ctype: &Type, types: &Types) -> SemanticResult<ExprType> {
    let expr = expr.const_fold(types)?;
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
    types: &Types,
    location: &Location,
) -> SemanticResult<ExprType> {
    let (left, right) = (left.const_fold(types)?, right.const_fold(types)?);
    if let ExprType::Literal(token) = right.expr {
        let shift = match token.non_negative_int() {
            Ok(u) => u,
            Err(_) => err!(
                "cannot shift left by a negative amount".into(),
                location.clone()
            ),
        };
        let sizeof = ctype.sizeof(types).map_err(|err| Locatable {
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
    types: &Types,
    location: &Location,
) -> SemanticResult<ExprType> {
    let (left, right) = (left.const_fold(types)?, right.const_fold(types)?);
    if let ExprType::Literal(token) = right.expr {
        let shift = match token.non_negative_int() {
            Ok(u) => u,
            Err(_) => err!(
                "cannot shift left by a negative amount".into(),
                location.clone()
            ),
        };
        if types[left.ctype].is_signed() {
            let size = match types[left.ctype].sizeof(types) {
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
