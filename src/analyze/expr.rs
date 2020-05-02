use super::Analyzer;
use crate::data::{hir::*, lex::ComparisonToken, *};
use crate::intern::InternedStr;
use crate::parse::Lexer;

use target_lexicon::Triple;

impl<T: Lexer> Analyzer<T> {
    pub fn parse_expr(&mut self, expr: ast::Expr) -> Expr {
        use ast::ExprType::*;
        match expr.data {
            // 1 | "str" | 'a'
            Literal(lit) => literal(lit, expr.location),
            // x
            Id(id) => self.parse_id(id, expr.location),
            // (int)x
            Cast(ctype, inner) => {
                let ctype = self.parse_typename(ctype, expr.location);
                self.explicit_cast(*inner, ctype)
            }
            Shift(left, right, direction) => {
                let op = if direction {
                    BinaryOp::Shl
                } else {
                    BinaryOp::Shr
                };
                self.binary_helper(left, right, op, Self::parse_integer_op)
            }
            BitwiseAnd(left, right) => {
                self.binary_helper(left, right, BinaryOp::BitwiseAnd, Self::parse_integer_op)
            }
            BitwiseOr(left, right) => {
                self.binary_helper(left, right, BinaryOp::BitwiseOr, Self::parse_integer_op)
            }
            Xor(left, right) => {
                self.binary_helper(left, right, BinaryOp::Xor, Self::parse_integer_op)
            }
            Compare(left, right, token) => self.relational_expr(*left, *right, token),
            Mul(left, right) => self.binary_helper(left, right, BinaryOp::Mul, Self::mul),
            Div(left, right) => self.binary_helper(left, right, BinaryOp::Div, Self::mul),
            Mod(left, right) => self.binary_helper(left, right, BinaryOp::Mod, Self::mul),
            Assign(lval, rval, token) => {
                let lval = self.parse_expr(*lval);
                let rval = self.parse_expr(*rval);
                self.assignment_expr(lval, rval, token, expr.location)
            }
            Add(left, right) => self.binary_helper(left, right, BinaryOp::Add, Self::add),
            Sub(left, right) => self.binary_helper(left, right, BinaryOp::Sub, Self::add),
            FuncCall(func, args) => self.func_call(*func, args),
            Member(struct_, id) => {
                let struct_ = self.parse_expr(*struct_);
                self.struct_member(struct_, id, expr.location)
            }
            // s->p desguars to (*s).p
            DerefMember(inner, id) => {
                let inner = self.parse_expr(*inner);
                let struct_type = match &inner.ctype {
                    Type::Pointer(ctype, _) => match &**ctype {
                        Type::Union(_) | Type::Struct(_) => (**ctype).clone(),
                        other => {
                            self.err(SemanticError::NotAStruct(other.clone()), inner.location);
                            return inner;
                        }
                    },
                    other => {
                        self.err(SemanticError::NotAPointer(other.clone()), inner.location);
                        return inner;
                    }
                };
                // NOTE: when we pass `deref` to `struct_member`,
                // it will always mark the resulting expression as an `lval`.
                // To avoid a double dereference, we mark `deref` as an `rval`.
                let deref = inner.indirection(false, struct_type);
                self.struct_member(deref, id, expr.location)
            }
            // `*p` or `a[i]`
            Deref(inner) => {
                let inner = self.parse_expr(*inner);
                match &inner.ctype {
                    Type::Array(t, _) | Type::Pointer(t, _) => {
                        let ctype = (**t).clone();
                        inner.indirection(true, ctype)
                    }
                    _ => {
                        self.err(
                            SemanticError::NotAPointer(inner.ctype.clone()),
                            expr.location,
                        );
                        inner
                    }
                }
            }
            // &x
            // 6.5.3.2 Address and indirection operators
            AddressOf(inner) => {
                let inner = self.parse_expr(*inner);
                match inner.expr {
                    // parse &*x as x
                    // footnote 102: &*E is equivalent to E (even if E is a null pointer)
                    ExprType::Deref(double_inner) => *double_inner,
                    // footnote 121:
                    // > the address of any part of an object declared with storage-class specifier register cannot be computed,
                    // > either explicitly (by use of the unary & operator as discussed in 6.5.3.2)
                    // > or implicitly (by converting an array name to a pointer as discussed in 6.3.2.1).
                    ExprType::Id(ref sym) if sym.get().storage_class == StorageClass::Register => {
                        self.err(
                            SemanticError::InvalidAddressOf("variable declared with `register`"),
                            expr.location,
                        );
                        inner
                    }
                    // > The operand of the unary & operator shall be either a function designator,
                    // > the result of a [] or unary * operator,
                    // > or an lvalue that designates an object that is not a bit-field and is not declared with the register storage-class specifier.
                    _ if inner.lval => Expr {
                        lval: false,
                        location: expr.location,
                        ctype: Type::Pointer(Box::new(inner.ctype.clone()), Qualifiers::default()),
                        expr: inner.expr,
                    },
                    _ => {
                        self.err(SemanticError::InvalidAddressOf("value"), expr.location);
                        inner
                    }
                }
            }
            // ++x
            PreIncrement(inner, increment) => {
                self.increment_op(true, increment, *inner, expr.location)
            }
            // x++
            PostIncrement(inner, increment) => {
                self.increment_op(false, increment, *inner, expr.location)
            }
            // a[i]
            Index(left, right) => self.index(*left, *right, expr.location),
            AlignofType(type_name) => {
                let ctype = self.parse_typename(type_name, expr.location);
                self.align(ctype, expr.location)
            }
            AlignofExpr(inner) => {
                let inner = self.parse_expr(*inner);
                self.align(inner.ctype, expr.location)
            }
            SizeofType(type_name) => {
                let ctype = self.parse_typename(type_name, expr.location);
                self.sizeof(ctype, expr.location)
            }
            SizeofExpr(inner) => {
                let inner = self.parse_expr(*inner);
                self.sizeof(inner.ctype, expr.location)
            }
            BitwiseNot(inner) => self.bitwise_not(*inner),
            UnaryPlus(inner) => self.unary_add(*inner, true, expr.location),
            Negate(inner) => self.unary_add(*inner, false, expr.location),
            // !x
            LogicalNot(inner) => self.logical_not(*inner),
            // x && y
            LogicalAnd(left, right) => {
                self.binary_helper(left, right, BinaryOp::LogicalAnd, Self::logical_bin_op)
            }
            // x || y
            LogicalOr(left, right) => {
                self.binary_helper(left, right, BinaryOp::LogicalOr, Self::logical_bin_op)
            }
            // x, y
            // evaluate x, discarding its value, then yield the value of y
            // mostly used to have multiple side effects in a single statement, such as in a for loop:
            // `for(j = i, k = 0; k < n; j++, k++);`
            // see also https://stackoverflow.com/a/43561555/7669110
            Comma(left, right) => {
                let left = self.parse_expr(*left);
                let right = self.parse_expr(*right).rval();
                Expr {
                    ctype: right.ctype.clone(),
                    lval: false,
                    expr: ExprType::Comma(Box::new(left), Box::new(right)),
                    location: expr.location,
                }
            }
            Ternary(condition, then, otherwise) => {
                self.ternary(*condition, *then, *otherwise, expr.location)
            }
        }
    }
    // only meant for use with `parse_expr`
    // TODO: change ast::Expr to use `ExprType::Binary` as well, which would make this unnecessary
    // TODO: these functions should have the locations of the parent expression, not the children
    #[allow(clippy::boxed_local)]
    fn binary_helper<F>(
        &mut self,
        left: Box<ast::Expr>,
        right: Box<ast::Expr>,
        op: BinaryOp,
        expr_checker: F,
    ) -> Expr
    where
        F: FnOnce(&mut Self, Expr, Expr, BinaryOp) -> Expr,
    {
        let left = self.parse_expr(*left);
        let right = self.parse_expr(*right);
        expr_checker(self, left, right, op)
    }
    // left OP right, where OP is an operation that requires integral types
    fn parse_integer_op(&mut self, left: Expr, right: Expr, op: BinaryOp) -> Expr {
        let non_scalar = if !left.ctype.is_integral() {
            Some(&left.ctype)
        } else if !right.ctype.is_integral() {
            Some(&right.ctype)
        } else {
            None
        };
        let location = left.location.merge(right.location);
        if let Some(ctype) = non_scalar {
            self.err(SemanticError::NonIntegralExpr(ctype.clone()), location);
        }
        let (promoted_expr, next) = self.binary_promote(left, right);
        Expr {
            ctype: next.ctype.clone(),
            expr: ExprType::Binary(op, Box::new(promoted_expr), Box::new(next)),
            lval: false,
            location,
        }
    }
    // x
    fn parse_id(&mut self, name: InternedStr, location: Location) -> Expr {
        let mut pretend_zero = Expr::zero(location);
        pretend_zero.ctype = Type::Error;
        match self.scope.get(&name) {
            None => {
                self.err(SemanticError::UndeclaredVar(name), location);
                pretend_zero
            }
            Some(&symbol) => {
                let meta = symbol.get();
                // typedef int i; return i + 1;
                if meta.storage_class == StorageClass::Typedef {
                    self.err(SemanticError::TypedefInExpressionContext, location);
                    return pretend_zero;
                }
                if let Type::Enum(ident, members) = &meta.ctype {
                    let mapper = |(member, value): &(InternedStr, i64)| {
                        if name == *member {
                            Some(*value)
                        } else {
                            None
                        }
                    };
                    let enumerator = members.iter().find_map(mapper);
                    // enum e { A }; return A;
                    if let Some(e) = enumerator {
                        return Expr {
                            ctype: Type::Enum(*ident, members.clone()),
                            location,
                            lval: false,
                            expr: ExprType::Literal(Literal::Int(e)),
                        };
                    }
                    // otherwise, `enum e { A } my_e; return my_e;`
                }
                Expr::id(symbol, location)
            }
        }
    }
    // `left == right`, `left < right`, or similar
    // 6.5.9 Equality operators
    fn relational_expr(
        &mut self,
        left: ast::Expr,
        right: ast::Expr,
        token: ComparisonToken,
    ) -> Expr {
        let location = left.location.merge(right.location);
        let mut left = self.parse_expr(left);
        let mut right = self.parse_expr(right);

        // i == i
        if left.ctype.is_arithmetic() && right.ctype.is_arithmetic() {
            let tmp = self.binary_promote(left, right);
            left = tmp.0;
            right = tmp.1;
        } else {
            let (left_expr, right_expr) = (left.rval(), right.rval());
            // p1 == p2
            if !((left_expr.ctype.is_pointer() && left_expr.ctype == right_expr.ctype)
                // equality operations have different rules :(
                || ((token == ComparisonToken::EqualEqual || token == ComparisonToken::NotEqual)
                    // shoot me now
                    // (int*)p1 == (void*)p2
                    && ((left_expr.ctype.is_pointer() && right_expr.ctype.is_void_pointer())
                        // (void*)p1 == (int*)p2
                        || (left_expr.ctype.is_void_pointer() && right_expr.ctype.is_pointer())
                        // NULL == (int*)p2
                        || (left_expr.is_null() && right_expr.ctype.is_pointer())
                        // (int*)p1 == NULL
                        || (left_expr.ctype.is_pointer() && right_expr.is_null()))))
            {
                self.err(
                    SemanticError::InvalidRelationalType(
                        token,
                        left_expr.ctype.clone(),
                        right_expr.ctype.clone(),
                    ),
                    location,
                );
            }
            left = left_expr;
            right = right_expr;
        }
        assert!(!left.lval && !right.lval);
        Expr {
            lval: false,
            location,
            ctype: Type::Bool,
            expr: ExprType::Binary(BinaryOp::Compare(token), Box::new(left), Box::new(right)),
        }
    }
    // `left OP right`, where OP is Mul, Div, or Mod
    // 6.5.5 Multiplicative operators
    fn mul(&mut self, left: Expr, right: Expr, op: BinaryOp) -> Expr {
        let location = left.location.merge(right.location);

        if op == BinaryOp::Mod && !(left.ctype.is_integral() && right.ctype.is_integral()) {
            self.err(
                SemanticError::from(format!(
                    "expected integers for both operators of %, got '{}' and '{}'",
                    left.ctype, right.ctype
                )),
                location,
            );
        } else if !(left.ctype.is_arithmetic() && right.ctype.is_arithmetic()) {
            self.err(
                SemanticError::from(format!(
                    "expected float or integer types for both operands of {}, got '{}' and '{}'",
                    op, left.ctype, right.ctype
                )),
                location,
            );
        }
        let (left, right) = self.binary_promote(left, right);
        Expr {
            ctype: left.ctype.clone(),
            location,
            lval: false,
            expr: ExprType::Binary(op, Box::new(left), Box::new(right)),
        }
    }
    // `a + b` or `a - b`
    // `op` should only be `Add` or `Sub`
    // 6.5.6 Additive operators
    fn add(&mut self, mut left: Expr, mut right: Expr, op: BinaryOp) -> Expr {
        let is_add = op == BinaryOp::Add;
        let location = left.location.merge(right.location);
        match (&left.ctype, &right.ctype) {
            // `p + i`
            (Type::Pointer(to, _), i)
            | (Type::Array(to, _), i) if i.is_integral() && to.is_complete() => {
                let to = to.clone();
                let (left, right) = (left.rval(), right.rval());
                return self.pointer_arithmetic(left, right, &*to, location);
            }
            // `i + p`
            (i, Type::Pointer(to, _))
                // `i - p` for pointer p is not valid
            | (i, Type::Array(to, _)) if i.is_integral() && is_add && to.is_complete() => {
                let to = to.clone();
                let (left, right) = (left.rval(), right.rval());
                return self.pointer_arithmetic(right, left, &*to, location);
            }
            _ => {}
        };
        // `i + i`
        let (ctype, lval) = if left.ctype.is_arithmetic() && right.ctype.is_arithmetic() {
            let tmp = self.binary_promote(left, right);
            left = tmp.0;
            right = tmp.1;
            (left.ctype.clone(), false)
        // `p1 - p2`
        // `p1 + p2` for pointers p1 and p2 is not valid
        } else if !is_add && left.ctype.is_pointer_to_complete_object() && left.ctype == right.ctype
        {
            // not sure what type to use here, C11 standard doesn't mention it
            (left.ctype.clone(), true)
        } else {
            self.err(
                SemanticError::InvalidAdd(op, left.ctype.clone(), right.ctype.clone()),
                location,
            );
            (left.ctype.clone(), false)
        };
        Expr {
            ctype,
            lval,
            location,
            expr: ExprType::Binary(op, Box::new(left), Box::new(right)),
        }
    }
    // (int)i
    // 6.5.4 Cast operators
    fn explicit_cast(&mut self, expr: ast::Expr, ctype: Type) -> Expr {
        let location = expr.location;
        let expr = self.parse_expr(expr).rval();
        // (void)0;
        if ctype == Type::Void {
            // casting anything to void is allowed
            return Expr {
                lval: false,
                ctype,
                // this just signals to the backend to ignore this outer expr
                expr: ExprType::Cast(Box::new(expr)),
                location,
            };
        }
        // (struct s)1
        if !ctype.is_scalar() {
            self.err(SemanticError::NonScalarCast(ctype.clone()), location);
        // (int*)1.0
        } else if expr.ctype.is_floating() && ctype.is_pointer()
            // (float)(int*)p
            || expr.ctype.is_pointer() && ctype.is_floating()
        {
            self.err(SemanticError::FloatPointerCast(ctype.clone()), location);
        // struct { int i; } s; (int)s
        } else if expr.ctype.is_struct() {
            // not implemented: galaga (https://github.com/jyn514/rcc/issues/98)
            self.err(SemanticError::StructCast, location);
        // void f(); (int)f();
        } else if expr.ctype == Type::Void {
            self.err(SemanticError::VoidCast, location);
        }
        Expr {
            lval: false,
            expr: ExprType::Cast(Box::new(expr)),
            ctype,
            location,
        }
    }
    // `base + index`, where `pointee` is the type of `*base`
    // 6.5.6 Additive operators
    fn pointer_arithmetic(
        &mut self,
        base: Expr,
        index: Expr,
        pointee: &Type,
        location: Location,
    ) -> Expr {
        // the idea is to desugar to `base + sizeof(base)*index`
        let offset = Expr {
            lval: false,
            location: index.location,
            expr: ExprType::Cast(Box::new(index)),
            ctype: base.ctype.clone(),
        }
        .rval();
        let size = match pointee.sizeof(&self.target) {
            Ok(s) => s,
            Err(_) => {
                self.err(
                    SemanticError::PointerAddUnknownSize(base.ctype.clone()),
                    location,
                );
                1
            }
        };
        let size_literal = literal(Literal::UnsignedInt(size), offset.location);
        let size_cast = Expr {
            lval: false,
            location: offset.location,
            ctype: offset.ctype.clone(),
            expr: ExprType::Cast(Box::new(size_literal)),
        };
        let offset = Expr {
            lval: false,
            location: offset.location,
            ctype: offset.ctype.clone(),
            expr: ExprType::Binary(BinaryOp::Mul, Box::new(size_cast), Box::new(offset)),
        };
        Expr {
            lval: false,
            location,
            ctype: base.ctype.clone(),
            expr: ExprType::Binary(BinaryOp::Add, Box::new(base), Box::new(offset)),
        }
    }
    // `func(args)`
    // 6.5.2.2 Function calls
    fn func_call(&mut self, func: ast::Expr, args: Vec<ast::Expr>) -> Expr {
        let mut func = self.parse_expr(func);
        // if fp is a function pointer, fp() desugars to (*fp)()
        match &func.ctype {
            Type::Pointer(pointee, _) if pointee.is_function() => {
                func = Expr {
                    lval: false,
                    location: func.location,
                    ctype: (**pointee).clone(),
                    expr: ExprType::Deref(Box::new(func)),
                }
            }
            _ => {}
        };
        let functype = match &func.ctype {
            Type::Function(functype) => functype,
            Type::Error => return func, // we've already reported this error
            other => {
                self.err(SemanticError::NotAFunction(other.clone()), func.location);
                return func;
            }
        };
        let mut expected = functype.params.len();
        // f(void)
        if expected == 1 && functype.params[0].get().ctype == Type::Void {
            expected = 0;
        }
        // f() takes _any_ number of arguments
        if !functype.params.is_empty()
            // `int f(int); f()` or `int f(int); f(1, 2)`
            && (args.len() < expected || args.len() > expected && !functype.varargs)
        {
            self.err(
                SemanticError::WrongArgumentNumber(args.len(), expected),
                func.location,
            );
        }
        let mut promoted_args = vec![];
        for (i, arg) in args.into_iter().enumerate() {
            let arg = self.parse_expr(arg);
            let promoted = match functype.params.get(i) {
                // int f(int); f(1)
                Some(expected) => arg
                    .rval()
                    .implicit_cast(&expected.get().ctype, &mut self.error_handler),
                // `int f(); f(1)` or `int f(int, ...); f(1, 2)`
                None => self.default_promote(arg),
            };
            promoted_args.push(promoted);
        }
        Expr {
            location: func.location,
            lval: false, // no move semantics here!
            ctype: *functype.return_type.clone(),
            expr: ExprType::FuncCall(Box::new(func), promoted_args),
        }
    }
    /// 'default promotions' from 6.5.2.2p6
    fn default_promote(&mut self, expr: Expr) -> Expr {
        let expr = expr.rval();
        let ctype = expr.ctype.clone().default_promote(&self.target);
        expr.implicit_cast(&ctype, &mut self.error_handler)
    }
    // parse a struct member
    // used for both s.a and s->a
    // 6.5.2.3 Structure and union members
    fn struct_member(&mut self, expr: Expr, id: InternedStr, location: Location) -> Expr {
        match &expr.ctype {
            Type::Struct(stype) | Type::Union(stype) => {
                let members = stype.members();
                // struct s; s.a
                if members.is_empty() {
                    self.err(
                        SemanticError::IncompleteDefinitionUsed(expr.ctype.clone()),
                        location,
                    );
                    expr
                // struct s { int i; }; s.i
                } else if let Some(member) = members.iter().find(|member| member.id == id) {
                    Expr {
                        ctype: member.ctype.clone(),
                        lval: true,
                        location,
                        expr: ExprType::Member(Box::new(expr), id),
                    }
                // struct s { int i; }; s.j
                } else {
                    self.err(SemanticError::NotAMember(id, expr.ctype.clone()), location);
                    expr
                }
            }
            // (1).a
            _ => {
                self.err(SemanticError::NotAStruct(expr.ctype.clone()), location);
                expr
            }
        }
    }
    // ++i, i--
    // 6.5.2.4 Postfix increment and decrement operators
    fn increment_op(
        &mut self,
        prefix: bool,
        increment: bool,
        expr: ast::Expr,
        location: Location,
    ) -> Expr {
        use crate::data::lex::AssignmentToken;

        let expr = self.parse_expr(expr);
        if let Err(err) = expr.modifiable_lval() {
            self.err(err, location);
        } else if !(expr.ctype.is_arithmetic() || expr.ctype.is_pointer()) {
            self.err(
                SemanticError::InvalidIncrement(expr.ctype.clone()),
                expr.location,
            );
        }
        // ++i is syntactic sugar for i+=1
        if prefix {
            let rval = Expr {
                lval: false,
                ctype: expr.ctype.clone(),
                location,
                expr: ExprType::Cast(Box::new(literal(Literal::Int(1), location))),
            };
            let op = if increment {
                AssignmentToken::AddEqual
            } else {
                AssignmentToken::SubEqual
            };
            self.assignment_expr(expr, rval, op, location)
        // i++ requires support from the backend
        // 6.5.2.4 Postfix increment and decrement operators
        // evaluate the rvalue of `i` and as a side effect, increment the value at the stored address
        // ex: `int i = 0, j; j = i++;` leaves a value of 0 in j and a value of 1 in i
        } else {
            Expr {
                lval: false,
                ctype: expr.ctype.clone(),
                // true, false: increment/decrement
                expr: ExprType::PostIncrement(Box::new(expr), increment),
                location,
            }
        }
    }
    // a[i] desugars to *(a + i)
    // 6.5.2.1 Array subscripting
    fn index(&mut self, left: ast::Expr, right: ast::Expr, location: Location) -> Expr {
        let left = self.parse_expr(left).rval();
        let right = self.parse_expr(right).rval();

        let (target_type, array, index) = match (&left.ctype, &right.ctype) {
            // p[i]
            (Type::Pointer(target, _), _) => ((**target).clone(), left, right),
            // i[p]
            (_, Type::Pointer(target, _)) => ((**target).clone(), right, left),
            (l, _) => {
                self.err(SemanticError::NotAPointer(l.clone()), location);
                return left;
            }
        };
        let mut addr = self.pointer_arithmetic(array, index, &target_type, location);
        addr.ctype = target_type;
        // `p + i` -> `*(p + i)`
        addr.lval = true;
        addr
    }
    // _Alignof(int)
    fn align(&mut self, ctype: Type, location: Location) -> Expr {
        let align = ctype.alignof(&self.target).unwrap_or_else(|err| {
            self.err(err.into(), location);
            1
        });
        literal(Literal::UnsignedInt(align), location)
    }
    // sizeof(int)
    // 6.5.3.4 The sizeof and _Alignof operators
    fn sizeof(&mut self, ctype: Type, location: Location) -> Expr {
        let align = ctype.sizeof(&self.target).unwrap_or_else(|err| {
            self.err(err.into(), location);
            1
        });
        literal(Literal::UnsignedInt(align), location)
    }
    // ~expr
    // 6.5.3.3 Unary arithmetic operators
    fn bitwise_not(&mut self, expr: ast::Expr) -> Expr {
        let expr = self.parse_expr(expr);
        if !expr.ctype.is_integral() {
            self.err(
                SemanticError::NonIntegralExpr(expr.ctype.clone()),
                expr.location,
            );
            expr
        } else {
            let expr = self.integer_promote(expr);
            Expr {
                lval: false,
                ctype: expr.ctype.clone(),
                location: expr.location,
                expr: ExprType::BitwiseNot(Box::new(expr)),
            }
        }
    }
    // -x and +x
    // 6.5.3.3 Unary arithmetic operators
    fn unary_add(&mut self, expr: ast::Expr, add: bool, location: Location) -> Expr {
        let expr = self.parse_expr(expr);
        if !expr.ctype.is_arithmetic() {
            self.err(SemanticError::NotArithmetic(expr.ctype.clone()), location);
            return expr;
        }
        let expr = self.integer_promote(expr);
        if add {
            Expr {
                lval: false,
                location,
                ..expr
            }
        } else {
            Expr {
                lval: false,
                ctype: expr.ctype.clone(),
                location,
                expr: ExprType::Negate(Box::new(expr)),
            }
        }
    }
    // !expr
    // 6.5.3.3 Unary arithmetic operators
    // > The expression !E is equivalent to (0==E).
    fn logical_not(&mut self, expr: ast::Expr) -> Expr {
        let expr = self.parse_expr(expr);
        let boolean = expr.truthy(&mut self.error_handler);
        debug_assert_eq!(boolean.ctype, Type::Bool);
        let zero = Expr::zero(boolean.location).implicit_cast(&Type::Bool, &mut self.error_handler);
        Expr {
            lval: false,
            location: boolean.location,
            ctype: Type::Bool,
            expr: ExprType::Binary(
                BinaryOp::Compare(ComparisonToken::EqualEqual),
                Box::new(boolean),
                Box::new(zero),
            ),
        }
    }
    // a || b or a && b
    // NOTE: this short circuits if possible
    // 6.5.14 Logical OR operator and 6.5.13 Logical AND operator
    fn logical_bin_op(&mut self, a: Expr, b: Expr, op: BinaryOp) -> Expr {
        let a = a.implicit_cast(&Type::Bool, &mut self.error_handler);
        let b = b.implicit_cast(&Type::Bool, &mut self.error_handler);
        Expr {
            lval: false,
            // TODO: this is wrong, it should be an int
            ctype: Type::Bool,
            location: a.location,
            expr: ExprType::Binary(op, Box::new(a), Box::new(b)),
        }
    }
    // condition ? then : otherwise
    // like an `if` in Rust: evaluate `condition`, yield the value of `then` if true, otherwise yield the value of `otherwise`
    fn ternary(
        &mut self,
        condition: ast::Expr,
        then: ast::Expr,
        otherwise: ast::Expr,
        location: Location,
    ) -> Expr {
        let condition = self.parse_expr(condition).truthy(&mut self.error_handler);
        let mut then = self.parse_expr(then).rval();
        let mut otherwise = self.parse_expr(otherwise).rval();

        if then.ctype.is_arithmetic() && otherwise.ctype.is_arithmetic() {
            let (tmp1, tmp2) = self.binary_promote(then, otherwise);
            then = tmp1;
            otherwise = tmp2;
        } else if !pointer_promote(&mut then, &mut otherwise) {
            self.err(
                SemanticError::IncompatibleTypes(then.ctype.clone(), otherwise.ctype.clone()),
                location,
            );
        }
        Expr {
            ctype: then.ctype.clone(),
            lval: false,
            location,
            expr: ExprType::Ternary(Box::new(condition), Box::new(then), Box::new(otherwise)),
        }
    }

    // `a = b` or `a += b`
    fn assignment_expr(
        &mut self,
        lval: Expr,
        rval: Expr,
        token: lex::AssignmentToken,
        location: Location,
    ) -> Expr {
        if let Err(err) = lval.modifiable_lval() {
            self.err(err, location);
        }
        // `a = b`
        if let lex::AssignmentToken::Equal = token {
            let mut rval = rval.rval();
            if rval.ctype != lval.ctype {
                rval = rval.implicit_cast(&lval.ctype, &mut self.error_handler);
            }
            return Expr {
                ctype: lval.ctype.clone(),
                lval: false, // `(i = j) = 4`; is invalid
                location,
                expr: ExprType::Binary(BinaryOp::Assign, Box::new(lval), Box::new(rval)),
            };
        }
        // Complex assignment is tricky because the left side needs to be evaluated only once
        // Consider e.g. `*f() += 1`: `f()` should only be called once.
        // The hack implemented here is to treat `*f()` as a variable then load and store it to memory:
        // `tmp = &f(); *tmp = *tmp + 1;`
        // see also footnote 113 which has a similar algorithm (but is more convoluted because of atomics)

        // declare tmp in a new hidden scope
        // We really should only be modifying the scope in `FunctionAnalyzer`,
        // but assignment expressions can never appear in an initializer anyway.
        self.scope.enter();
        let tmp_name = "tmp".into();
        let ctype = lval.ctype.clone();
        // TODO: we could probably make these qualifiers stronger
        let ptr_type = Type::Pointer(Box::new(ctype.clone()), Qualifiers::default());
        let meta = Metadata {
            id: tmp_name,
            ctype: ptr_type.clone(),
            qualifiers: Qualifiers::NONE,
            storage_class: StorageClass::Register,
        };
        let tmp_var = self.declare(meta, true, location);

        // NOTE: this does _not_ call rval() on `lval`
        // there's no way to do this in C natively - the closest is `&var`, but that doesn't work on expressions
        // `T tmp = &*f()` or `T tmp = &sum`
        let init = Some(Initializer::Scalar(Box::new(lval)));
        let decl = Declaration {
            symbol: tmp_var,
            init,
        };
        self.decl_side_channel.push(Locatable::new(decl, location));
        self.scope.exit();
        // load `tmp`, i.e. `&*f()`, only evaluated once
        let tmp = Expr {
            expr: ExprType::Id(tmp_var),
            ctype: ptr_type,
            lval: true,
            location,
        }
        // this `rval` is because we have the (pointless) address of `tmp`
        // instead we want the address of the lval
        .rval();

        // before we had `&sum`, now we have `sum`
        // `*tmp`, i.e. `*f()`
        let lval_as_rval = Expr {
            ctype: ctype.clone(),
            lval: false,
            location,
            // this clone is pretty cheap since `tmp_assign_expr` is just an id
            expr: ExprType::Deref(Box::new(tmp.clone())),
        };
        // `*tmp` in an lval context
        let target = tmp.indirection(true, ctype.clone());
        // `*tmp + 1`
        let new_val = self
            .desugar_op(lval_as_rval, rval.rval(), token)
            .implicit_cast(&target.ctype, &mut self.error_handler);

        // *tmp = *f() + 1
        Expr {
            ctype,
            lval: false,
            location,
            expr: ExprType::Binary(BinaryOp::Assign, Box::new(target), Box::new(new_val)),
        }
    }
    fn desugar_op(&mut self, left: Expr, right: Expr, token: lex::AssignmentToken) -> Expr {
        use lex::AssignmentToken::*;

        match token {
            Equal => unreachable!(),
            OrEqual => self.parse_integer_op(left, right, BinaryOp::BitwiseOr),
            AndEqual => self.parse_integer_op(left, right, BinaryOp::BitwiseAnd),
            XorEqual => self.parse_integer_op(left, right, BinaryOp::Xor),
            ShlEqual => self.parse_integer_op(left, right, BinaryOp::Shl),
            ShrEqual => self.parse_integer_op(left, right, BinaryOp::Shr),
            MulEqual => self.mul(left, right, BinaryOp::Mul),
            DivEqual => self.mul(left, right, BinaryOp::Div),
            ModEqual => self.mul(left, right, BinaryOp::Mod),
            AddEqual => self.add(left, right, BinaryOp::Add),
            SubEqual => self.add(left, right, BinaryOp::Sub),
        }
    }

    // Perform a binary conversion, including all relevant casts.
    //
    // See `Type::binary_promote` for conversion rules.
    fn binary_promote(&mut self, left: Expr, right: Expr) -> (Expr, Expr) {
        let (left, right) = (left.rval(), right.rval());
        let ctype = Type::binary_promote(left.ctype.clone(), right.ctype.clone(), &self.target);
        match ctype {
            Ok(promoted) => (
                left.implicit_cast(&promoted, &mut self.error_handler),
                right.implicit_cast(&promoted, &mut self.error_handler),
            ),
            Err(non_int) => {
                // TODO: this location is wrong
                self.err(SemanticError::NonIntegralExpr(non_int), right.location);
                (left, right)
            }
        }
    }

    // Perform an integer conversion, including all relevant casts.
    //
    // See `Type::integer_promote` for conversion rules.
    fn integer_promote(&mut self, expr: Expr) -> Expr {
        let expr = expr.rval();
        let ctype = expr.ctype.clone().integer_promote(&self.target);
        expr.implicit_cast(&ctype, &mut self.error_handler)
    }
}

// literal
pub(super) fn literal(literal: Literal, location: Location) -> Expr {
    use crate::data::types::ArrayType;

    let ctype = match &literal {
        Literal::Char(_) => Type::Char(true),
        Literal::Int(_) => Type::Long(true),
        Literal::UnsignedInt(_) => Type::Long(false),
        Literal::Float(_) => Type::Double,
        Literal::Str(s) => {
            let len = s.len() as u64;
            Type::Array(Box::new(Type::Char(true)), ArrayType::Fixed(len))
        }
    };
    Expr {
        lval: false,
        ctype,
        location,
        expr: ExprType::Literal(literal),
    }
}

fn pointer_promote(left: &mut Expr, right: &mut Expr) -> bool {
    if left.ctype == right.ctype {
        true
    } else if left.ctype.is_void_pointer() || left.ctype.is_char_pointer() || left.is_null() {
        left.ctype = right.ctype.clone();
        true
    } else if right.ctype.is_void_pointer() || right.ctype.is_char_pointer() || right.is_null() {
        right.ctype = left.ctype.clone();
        true
    } else {
        false
    }
}

impl Type {
    #[inline]
    fn is_void_pointer(&self) -> bool {
        match self {
            Type::Pointer(t, _) => **t == Type::Void,
            _ => false,
        }
    }
    #[inline]
    fn is_char_pointer(&self) -> bool {
        match self {
            Type::Pointer(t, _) => match **t {
                Type::Char(_) => true,
                _ => false,
            },
            _ => false,
        }
    }
    #[inline]
    /// used for pointer addition and subtraction, see section 6.5.6 of the C11 standard
    fn is_pointer_to_complete_object(&self) -> bool {
        match self {
            Type::Pointer(ctype, _) => ctype.is_complete() && !ctype.is_function(),
            Type::Array(_, _) => true,
            _ => false,
        }
    }
    /// Return whether self is a signed type.
    ///
    /// Should only be called on integral types.
    /// Calling sign() on a floating or derived type will return Err(()).
    fn sign(&self) -> Result<bool, ()> {
        use Type::*;
        match self {
            Char(sign) | Short(sign) | Int(sign) | Long(sign) => Ok(*sign),
            Bool => Ok(false),
            // TODO: allow enums with values of UINT_MAX
            Enum(_, _) => Ok(true),
            _ => Err(()),
        }
    }

    /// Return the rank of an integral type, according to section 6.3.1.1 of the C standard.
    ///
    /// It is an error to take the rank of a non-integral type.
    ///
    /// Examples:
    /// ```ignore
    /// use rcc::data::types::Type::*;
    /// assert!(Long(true).rank() > Int(true).rank());
    /// assert!(Int(false).rank() > Short(false).rank());
    /// assert!(Short(true).rank() > Char(true).rank());
    /// assert!(Char(true).rank() > Bool.rank());
    /// assert!(Long(false).rank() > Bool.rank());
    /// assert!(Long(true).rank() == Long(false).rank());
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
    // Subclause 2 of 6.3.1.1 Boolean, characters, and integers
    fn integer_promote(self, target: &Triple) -> Type {
        if self.rank() <= Type::Int(true).rank() {
            if Type::Int(true).can_represent(&self, target) {
                Type::Int(true)
            } else {
                Type::Int(false)
            }
        } else {
            self
        }
    }
    // 6.3.1.8 Usual arithmetic conversions
    fn binary_promote(mut left: Type, mut right: Type, target: &Triple) -> Result<Type, Type> {
        use Type::*;
        if left == Double || right == Double {
            return Ok(Double); // toil and trouble
        } else if left == Float || right == Float {
            return Ok(Float);
        }
        left = left.integer_promote(target);
        right = right.integer_promote(target);
        // TODO: we know that `left` can't be used after a move,
        // but rustc isn't smart enough to figure it out and let us remove the clone
        let signs = (
            left.sign().map_err(|_| left.clone())?,
            right.sign().map_err(|_| right.clone())?,
        );
        // same sign
        if signs.0 == signs.1 {
            return Ok(if left.rank() >= right.rank() {
                left
            } else {
                right
            });
        };
        let (signed, unsigned) = if signs.0 {
            (left, right)
        } else {
            (right, left)
        };
        if signed.can_represent(&unsigned, target) {
            Ok(signed)
        } else {
            Ok(unsigned)
        }
    }
    /// 6.5.2.2p6:
    /// > If the expression that denotes the called function has a type that does not include a prototype,
    /// > the integer promotions are performed on each argument,
    /// > and arguments that have type float are promoted to double.
    /// > These are called the default argument promotions.
    fn default_promote(self, target: &Triple) -> Type {
        if self.is_integral() {
            self.integer_promote(target)
        } else if self == Type::Float {
            Type::Double
        } else {
            self
        }
    }
    fn is_struct(&self) -> bool {
        match self {
            Type::Struct(_) | Type::Union(_) => true,
            _ => false,
        }
    }
    fn is_complete(&self) -> bool {
        match self {
            Type::Void | Type::Function(_) | Type::Array(_, types::ArrayType::Unbounded) => false,
            // TODO: update when we allow incomplete struct and union types (e.g. `struct s;`)
            _ => true,
        }
    }
}

impl Expr {
    pub(super) fn zero(location: Location) -> Expr {
        Expr {
            ctype: Type::Int(true),
            expr: ExprType::Literal(Literal::Int(0)),
            lval: false,
            location,
        }
    }
    // 6.3.2.3 Pointers
    fn is_null(&self) -> bool {
        // TODO: I think we need to const fold this to allow `(void*)0`
        if let ExprType::Literal(token) = &self.expr {
            match token {
                Literal::Int(0) | Literal::UnsignedInt(0) | Literal::Char(0) => true,
                _ => false,
            }
        } else {
            false
        }
    }
    fn id(symbol: MetadataRef, location: Location) -> Self {
        Self {
            expr: ExprType::Id(symbol),
            // TODO: maybe pass in the type as well to avoid the lookup?
            // but then we need to make sure the type matches the symbol
            ctype: symbol.get().ctype.clone(),
            lval: true,
            location,
        }
    }
    // Convert an expression to _Bool. Section 6.3.1.3 of the C standard:
    // "When any scalar value is converted to _Bool,
    // the result is 0 if the value compares equal to 0; otherwise, the result is 1."
    //
    // TODO: this looks like the same as casting to _Bool, can we just offload to the backend instead?
    //
    // if (expr)
    pub(crate) fn truthy(mut self, error_handler: &mut ErrorHandler) -> Expr {
        self = self.rval();
        if self.ctype == Type::Bool {
            return self;
        }
        if !self.ctype.is_scalar() {
            error_handler.error(
                SemanticError::Generic(format!(
                    "expression of type '{}' cannot be converted to bool",
                    self.ctype
                )),
                self.location,
            );
            self.ctype = Type::Error;
        }
        let zero = Expr::zero(self.location).implicit_cast(&self.ctype, error_handler);
        Expr {
            lval: false,
            location: self.location,
            ctype: Type::Bool,
            expr: ExprType::Binary(
                BinaryOp::Compare(ComparisonToken::NotEqual),
                Box::new(self),
                Box::new(zero),
            ),
        }
    }

    // ensure an expression has a value. convert
    // - arrays -> pointers
    // - functions -> pointers
    // - variables -> value stored in that variable
    // 6.3.2.1 Lvalues, arrays, and function designators
    // >  Except when it is the operand of [a bunch of different operators],
    // > an lvalue that does not have array type is converted to the value stored in the designated object (and is no longer an lvalue)
    pub(super) fn rval(self) -> Expr {
        match self.ctype {
            // a + 1 is the same as &a + 1
            Type::Array(to, _) => Expr {
                lval: false,
                ctype: Type::Pointer(to, Qualifiers::default()),
                ..self
            },
            Type::Function(_) => Expr {
                lval: false,
                ctype: Type::Pointer(
                    Box::new(self.ctype),
                    Qualifiers {
                        c_const: true,
                        ..Qualifiers::default()
                    },
                ),
                ..self
            },
            // HACK: structs can't be dereferenced since they're not scalar, so we just fake it
            Type::Struct(_) | Type::Union(_) if self.lval => Expr {
                lval: false,
                ..self
            },
            _ if self.lval => Expr {
                ctype: self.ctype.clone(),
                lval: false,
                location: self.location,
                expr: ExprType::Deref(Box::new(self)),
            },
            _ => self,
        }
    }
    // `*p` when p is a pointer
    //
    // NOTE: this can be in _either_ an lval or an rval context
    // in an rval context: `return *p;`
    // in an lval context: `*p = 1`
    //
    // `ctype` is the type of the resulting expression
    //
    // 6.5.3.2 Address and indirection operators
    fn indirection(self, lval: bool, ctype: Type) -> Self {
        Expr {
            location: self.location,
            ctype,
            lval,
            // this is super hacky but the only way I can think of to prevent
            // https://github.com/jyn514/rcc/issues/90
            // we need to call `self.rval()` so that if `self` is a variable we get its value, not its address.
            expr: ExprType::Noop(Box::new(self.rval())),
        }
    }

    // float f = (double)1.0
    // 6.3 Conversions
    pub(super) fn implicit_cast(self, ctype: &Type, error_handler: &mut ErrorHandler) -> Expr {
        let mut expr = self.rval();
        if &expr.ctype == ctype {
            expr
        // int -> long
        } else if expr.ctype.is_arithmetic() && ctype.is_arithmetic()
            // NULL -> int*
            || expr.is_null() && ctype.is_pointer()
            // if ((int*)p)
            || expr.ctype.is_pointer() && ctype.is_bool()
            // p -> void*
            || expr.ctype.is_pointer() && ctype.is_void_pointer()
            // p -> char*
            || expr.ctype.is_pointer() && ctype.is_char_pointer()
        {
            Expr {
                location: expr.location,
                expr: ExprType::Cast(Box::new(expr)),
                lval: false,
                ctype: ctype.clone(),
            }
        // `NULL -> int*` or `void* -> int*` or `char* -> int*`
        } else if ctype.is_pointer()
            && (expr.is_null() || expr.ctype.is_void_pointer() || expr.ctype.is_char_pointer())
        {
            expr.ctype = ctype.clone();
            expr
        } else if expr.ctype == Type::Error {
            expr
        } else {
            // allow implicit casts of const pointers
            // Standard (in the context `left = right`, i.e. casting `right` to `left`)
            // > the left operand has atomic, qualified, or unqualified pointer type,
            // > and (considering the type the left operand would have after lvalue conversion)
            // > both operands are pointers to qualified or unqualified versions of compatible types,
            // > and the type pointed to by the left has all the qualifiers of the type pointed to by the right;
            if let (Type::Pointer(a, from), Type::Pointer(b, to)) = (&expr.ctype, ctype) {
                if *a == *b && from.contains_all(*to) {
                    expr.ctype = ctype.clone();
                    return expr;
                }
            }
            error_handler.error(
                SemanticError::InvalidCast(expr.ctype.clone(), ctype.clone()),
                expr.location,
            );
            expr
        }
    }
    /// See section 6.3.2.1 of the C Standard. In particular:
    /// "A modifiable lvalue is an lvalue that does not have array type,
    /// does not  have an incomplete type, does not have a const-qualified type,
    /// and if it is a structure or union, does not have any member with a const-qualified type"
    fn modifiable_lval(&self) -> Result<(), SemanticError> {
        let err = |e| Err(SemanticError::NotAssignable(e));
        // rval
        if !self.lval {
            return err("rvalue".to_string());
        }
        // incomplete type
        if !self.ctype.is_complete() {
            return err(format!("expression with incomplete type '{}'", self.ctype));
        }
        // const-qualified type
        // TODO: handle `*const`
        if let ExprType::Id(sym) = &self.expr {
            let meta = sym.get();
            if meta.qualifiers.c_const {
                return err(format!("variable '{}' with `const` qualifier", meta.id));
            }
        }
        match &self.ctype {
            // array type
            Type::Array(_, _) => err("array".to_string()),
            // member with const-qualified type
            Type::Struct(stype) | Type::Union(stype) => {
                if stype
                    .members()
                    .iter()
                    .map(|sym| sym.qualifiers.c_const)
                    .any(|x| x)
                {
                    err("struct or union with `const` qualified member".to_string())
                } else {
                    Ok(())
                }
            }
            _ => Ok(()),
        }
    }
}

impl Qualifiers {
    // return whether `self` has all the qualifiers of `right`
    // WARNING: this _must_ be updated if you add more fields to `Qualifiers`
    fn contains_all(self, other: Self) -> bool {
        (self.c_const || !other.c_const) && (self.volatile || !other.volatile)
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::analyze::test::analyze;
    use crate::analyze::*;
    pub(crate) fn parse_expr(input: &str) -> CompileResult<Expr> {
        analyze(input, Parser::expr, Analyzer::parse_expr)
    }
    fn get_location(r: &CompileResult<Expr>) -> Location {
        match r {
            Ok(expr) => expr.location,
            Err(err) => err.location(),
        }
    }
    fn assert_literal(token: Literal) {
        let parsed = parse_expr(&token.to_string());
        let location = get_location(&parsed);
        assert_eq!(parsed.unwrap(), literal(token, location));
    }
    fn parse_expr_with_scope<'a>(input: &'a str, variables: &[MetadataRef]) -> CompileResult<Expr> {
        analyze(input, Parser::expr, |a, expr| {
            for &meta in variables {
                let id = meta.get().id;
                a.scope.insert(id, meta);
            }
            a.parse_expr(expr)
        })
    }
    fn assert_type(input: &str, ctype: Type) {
        match parse_expr(input) {
            Ok(expr) => assert_eq!(expr.ctype, ctype),
            Err(err) => panic!("error: {}", err.data),
        };
    }
    #[test]
    fn test_primaries() {
        assert_literal(Literal::Int(141));
        let parsed = parse_expr("\"hi there\"");

        assert_eq!(
            parsed,
            Ok(literal(
                Literal::Str("hi there\0".into()),
                get_location(&parsed)
            )),
        );
        assert_literal(Literal::Float(1.5));
        let parsed = parse_expr("(1)");
        assert_eq!(parsed, Ok(literal(Literal::Int(1), get_location(&parsed))));
        let x = Metadata {
            ctype: Type::Int(true),
            id: InternedStr::get_or_intern("x"),
            qualifiers: Default::default(),
            storage_class: Default::default(),
        }
        .insert();
        let parsed = parse_expr_with_scope("x", &[x]);
        assert_eq!(
            parsed,
            Ok(Expr {
                location: get_location(&parsed),
                ctype: Type::Int(true),
                lval: true,
                expr: ExprType::Id(x)
            })
        );
    }
    #[test]
    fn test_mul() {
        assert_type("1*1.0", Type::Double);
        assert_type("1*2.0 / 1.3", Type::Double);
        assert_type("3%2", Type::Long(true));
    }
    #[test]
    fn test_funcall() {
        let f = Metadata {
            id: InternedStr::get_or_intern("f"),
            qualifiers: Default::default(),
            storage_class: Default::default(),
            ctype: Type::Function(types::FunctionType {
                params: vec![Metadata {
                    ctype: Type::Void,
                    id: Default::default(),
                    qualifiers: Default::default(),
                    storage_class: StorageClass::Auto,
                }
                .insert()],
                return_type: Box::new(Type::Int(true)),
                varargs: false,
            }),
        }
        .insert();
        assert!(parse_expr_with_scope("f(1,2,3)", &[f]).is_err());
        let parsed = parse_expr_with_scope("f()", &[f]);
        assert!(match parsed {
            Ok(Expr {
                expr: ExprType::FuncCall(_, _),
                ..
            }) => true,
            _ => false,
        },);
    }
    #[test]
    fn test_type_errors() {
        assert!(parse_expr("1 % 2.0").is_err());
    }

    #[test]
    fn test_explicit_casts() {
        assert_type("(int)4.2", Type::Int(true));
        assert_type("(unsigned int)4.2", Type::Int(false));
        assert_type("(float)4.2", Type::Float);
        assert_type("(double)4.2", Type::Double);
        assert!(parse_expr("(int*)4.2").is_err());
        assert_type(
            "(int*)(int)4.2",
            Type::Pointer(Box::new(Type::Int(true)), Qualifiers::default()),
        );
    }
}
