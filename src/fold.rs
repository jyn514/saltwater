use crate::data::prelude::*;

macro_rules! fold_int_bin_op {
    ($left: expr, $right: expr, $constructor: expr, $op: tt) => {{
        let (left, right) = ($left.const_fold()?, $right.const_fold()?);
        match (&left.expr, &right.expr) {
            (ExprType::Literal(a), ExprType::Literal(b)) => {
                match (a, b) {
                    (Token::Int(a), Token::Int(b)) => ExprType::Literal(Token::Int(a $op b)),
                    (Token::Char(a), Token::Char(b)) => ExprType::Literal(Token::Char(a $op b)),
                    (_, _) => $constructor(Box::new(left), Box::new(right)),
                }
            }
            _ => $constructor(Box::new(left), Box::new(right)),
        }
    }}
}

macro_rules! fold_scalar_bin_op {
    ($left: expr, $right: expr, $constructor: ident, $op: tt) => {{
        let (left, right) = ($left.const_fold()?, $right.const_fold()?);
        match (&left.expr, &right.expr) {
            (ExprType::Literal(a), ExprType::Literal(b)) => {
                match (a, b) {
                    (Token::Int(a), Token::Int(b)) => ExprType::Literal(Token::Int(a $op b)),
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
) -> Result<ExprType, Locatable<String>>
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
($left: expr, $right: expr, $constructor: ident, $op: tt, $compare: expr) => {{
        let (left, right) = ($left.const_fold()?, $right.const_fold()?);
        match (&left.expr, &right.expr) {
            (ExprType::Literal(a), ExprType::Literal(b)) => {
                match (a, b) {
                    (Token::Int(a), Token::Int(b)) => ExprType::Literal(Token::Int((a $op b) as i64)),
                    #[allow(clippy::float_cmp)]
                    (Token::Float(a), Token::Float(b)) => ExprType::Literal(Token::Float(f64::from((a $op b) as u8))),
                    (Token::Char(a), Token::Char(b)) => ExprType::Literal(Token::Char((a $op b) as u8)),
                    // TODO: find a way to do this that allows `"hello" + 2 - 1`
                    //(Token::Str(s), Token::Int(i)) | (Token::Int(i), Token::Str(s)) => {
                    (_, _) => ExprType::$constructor(Box::new(left), Box::new(right), $compare),
                }
            }
            _ => ExprType::$constructor(Box::new(left), Box::new(right), $compare),
        }
    }}
}

impl Expr {
    // first result: whether the expression itself is erroneous
    // second result: whether the expression was constexpr
    pub fn constexpr(self) -> Result<Result<Locatable<Token>, Location>, Locatable<String>> {
        let folded = self.const_fold()?;
        let constexpr = match folded.expr {
            ExprType::Literal(token) => Ok(Locatable {
                data: token,
                location: folded.location,
            }),
            _ => Err(folded.location),
        };
        Ok(constexpr)
    }
    pub fn const_fold(self) -> Result<Expr, Locatable<String>> {
        let location = self.location;
        let folded = match self.expr {
            ExprType::Literal(_) => self.expr,
            // TODO: if a variable were const, could we const fold Ids?
            ExprType::Id(_) => self.expr,
            ExprType::Ref(expr) => ExprType::Ref(Box::new(expr.const_fold()?)),
            ExprType::Sizeof(ctype) => {
                let sizeof = ctype.sizeof().map_err(|data| Locatable {
                    data: data.into(),
                    location: location.clone(),
                })?;
                ExprType::Literal(Token::UnsignedInt(sizeof))
            }
            ExprType::Negate(expr) => {
                let expr = expr.const_fold()?;
                match expr.expr {
                    ExprType::Literal(Token::Int(i)) => ExprType::Literal(Token::Int(-i)),
                    ExprType::Literal(Token::Float(f)) => ExprType::Literal(Token::Float(-f)),
                    _ => ExprType::Negate(Box::new(expr)),
                }
            }
            ExprType::LogicalNot(expr) => lnot_fold(expr.const_fold()?),
            ExprType::BitwiseNot(expr) => {
                let expr = expr.const_fold()?;
                match expr.expr {
                    ExprType::Literal(Token::Int(i)) => ExprType::Literal(Token::Int(!i)),
                    _ => ExprType::BitwiseNot(Box::new(expr)),
                }
            }
            ExprType::Comma(left, right) => {
                let (left, right) = (left.const_fold()?, right.const_fold()?);
                // check if we can ignore left or it has side effects
                if left.constexpr {
                    right.expr
                } else {
                    ExprType::Comma(Box::new(left), Box::new(right))
                }
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
            ExprType::Add(left, right) => fold_scalar_bin_op!(left, right, Add, +),
            ExprType::Sub(left, right) => fold_scalar_bin_op!(left, right, Sub, -),
            ExprType::Mul(left, right) => fold_scalar_bin_op!(left, right, Mul, *),
            ExprType::Div(left, right) => fold_scalar_bin_op!(left, right, Div, /),

            ExprType::Mod(left, right) => fold_int_bin_op!(left, right, ExprType::Mod, %),
            ExprType::Xor(left, right) => fold_int_bin_op!(left, right, ExprType::Xor, ^),
            ExprType::BitwiseAnd(left, right) => {
                fold_int_bin_op!(left, right, ExprType::BitwiseAnd, &)
            }
            ExprType::BitwiseOr(left, right) => {
                fold_int_bin_op!(left, right, ExprType::BitwiseOr, |)
            }
            ExprType::Shift(left, right, true) => {
                fold_int_bin_op!(left, right, |left, right| ExprType::Shift(left, right, true), <<)
            }
            ExprType::Shift(left, right, false) => {
                fold_int_bin_op!(left, right, |left, right| ExprType::Shift(left, right, false), >>)
            }

            ExprType::Compare(left, right, Token::Less) => {
                fold_compare_op!(left, right, Compare, <, Token::Less)
            }
            ExprType::Compare(left, right, Token::LessEqual) => {
                fold_compare_op!(left, right, Compare, <=, Token::LessEqual)
            }
            ExprType::Compare(left, right, Token::Greater) => {
                fold_compare_op!(left, right, Compare, >, Token::Greater)
            }
            ExprType::Compare(left, right, Token::GreaterEqual) => {
                fold_compare_op!(left, right, Compare, >=, Token::GreaterEqual)
            }
            ExprType::Compare(left, right, Token::EqualEqual) => {
                fold_compare_op!(left, right, Compare, ==, Token::EqualEqual)
            }
            ExprType::Compare(left, right, Token::NotEqual) => {
                fold_compare_op!(left, right, Compare, !=, Token::NotEqual)
            }
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
                    .collect::<Result<_, Locatable<String>>>()?;
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
            ExprType::Increment(expr, pre, post) => {
                let expr = expr.const_fold()?;
                // this isn't constant for the same reason assignment isn't constant
                ExprType::Increment(Box::new(expr), pre, post)
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

fn cast(expr: Expr, ctype: &Type) -> Result<ExprType, Locatable<String>> {
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
