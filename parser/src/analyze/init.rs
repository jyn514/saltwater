use super::Analyzer;
use crate::data::{ast, error::SemanticError, hir::*, types, Location, Type};

impl Analyzer {
    pub(super) fn parse_initializer(
        &mut self, init: ast::Initializer, ctype: &Type, location: Location,
    ) -> Initializer {
        use ast::Initializer::{Aggregate, Scalar};
        // initializer_list
        let mut expr = match init {
            Aggregate(list) => return self.check_aggregate_overflow(list, ctype, location),
            Scalar(expr) => self.parse_expr(*expr),
        };
        // The only time (that I know of) that an expression will initialize a non-scalar
        // is for character literals.
        let is_char_array = match ctype {
            Type::Array(inner, _) => inner.is_char(),
            _ => false,
        };
        // See section 6.7.9 of the C11 standard:
        // The initializer for a scalar shall be a single expression, optionally enclosed in braces.
        // The initial value of the object is that of the expression (after conversion)
        if !is_char_array {
            expr = expr
                .rval()
                // if ctype is not a scalar, this will report an error, so we don't have to handle it specially
                .implicit_cast(ctype, &mut self.error_handler);
        }
        if !expr.lval && self.scope.is_global() && ctype.is_pointer() {
            expr = Expr {
                lval: false,
                location: expr.location,
                ctype: expr.ctype.clone(),
                expr: ExprType::StaticRef(Box::new(expr)),
            };
        }
        Initializer::Scalar(Box::new(expr))
    }

    fn check_aggregate_overflow(
        &mut self, list: Vec<ast::Initializer>, ctype: &Type, location: Location,
    ) -> Initializer {
        let len = list.len();
        let mut iter = list.into_iter().peekable();
        let init = self.aggregate_initializer(&mut iter, ctype, location);
        let leftover = iter.count();
        if leftover > 0 {
            self.err(SemanticError::TooManyMembers(len - leftover, len), location);
        }
        init
    }

    // handle char[][3] = {{1,2,3}}, but also = {1,2,3} and {{1}, 2, 3}
    // NOTE: this does NOT consume {} except for sub-elements
    fn aggregate_initializer(
        &mut self, list: &mut std::iter::Peekable<impl Iterator<Item = ast::Initializer>>,
        elem_type: &Type, location: Location,
    ) -> Initializer {
        use ast::Initializer::{Aggregate, Scalar};

        let mut elems = vec![];
        if list.peek().is_none() {
            self.err(SemanticError::EmptyInitializer, location);
            return Initializer::InitializerList(elems);
        }
        // char [][3] = {1};
        while let Some(elem) = list.peek() {
            let inner = elem_type.type_at(elems.len()).unwrap_or_else(|err| {
                self.err(err, location);
                Type::Error
            });
            // int a[][3] = {{1,2,3}}
            //               ^
            // initializer is aggregate, type errors will be caught later

            // If the initializer of a subaggregate or contained union begins with a left brace,
            // the initializers enclosed by that brace and its matching right brace initialize
            // the elements or members of the subaggregate or the contained union.
            let next = match elem {
                Aggregate(_) => match list.next() {
                    Some(Aggregate(inner_list)) => {
                        self.check_aggregate_overflow(inner_list, &inner, location)
                    }
                    _ => unreachable!(),
                },
                Scalar(_) => {
                    // int a[][3] = {1,2,3}
                    //               ^
                    // type is aggregate and initializer is scalar
                    // see if we can short circuit int[][3] -> int[3]
                    if inner != Type::Error && !inner.is_scalar() {
                        // Note: this element is _not_ consumed
                        self.aggregate_initializer(list, &inner, location)
                    // type is scalar and initializer is scalar
                    // int a[][3] = {{1,2,3}}
                    } else {
                        let expr = match list.next() {
                            Some(Scalar(expr)) => self.parse_expr(*expr),
                            _ => unreachable!(),
                        };
                        // scalar
                        Initializer::Scalar(Box::new(expr))
                    }
                }
            };
            elems.push(next);

            // Otherwise, only enough initializers from the list are taken
            // to account for the elements or members of the subaggregate
            // or the first member of the contained union;
            // any remaining initializers are left to initialize the next
            // element or member of the aggregate of which the current
            // subaggregate or contained union is a part.
            if elems.len() == elem_type.type_len() {
                break;
            }
        }
        Initializer::InitializerList(elems)
    }
}

impl Type {
    /// Given a type, return the maximum number of initializers for that type
    fn type_len(&self) -> usize {
        use types::ArrayType;
        match self {
            ty if ty.is_scalar() => 1,
            Type::Array(_, ArrayType::Fixed(size)) => *size as usize,
            Type::Array(_, ArrayType::Unbounded) => 0,
            Type::Struct(st) | Type::Union(st) => st.members().len(),
            Type::Error => 1,
            _ => unimplemented!("type checking for {}", self),
        }
    }
    /// Given a type and an index,
    /// return the type expected at that index in the initializer.
    ///
    /// e.g. if `struct s { int i; float f; };` is in scope,
    /// `type_at(s, 0)` will be `int` and `type_at(s, 1)` will be `float`
    fn type_at(&self, index: usize) -> Result<Type, SemanticError> {
        match self {
            ty if ty.is_scalar() => {
                if index == 0 {
                    Ok(ty.clone())
                } else {
                    Err(SemanticError::AggregateInitializingScalar(
                        ty.clone(),
                        index + 1,
                    ))
                }
            }
            Type::Array(inner, _) => Ok((**inner).clone()),
            Type::Struct(struct_type) => {
                let symbols = struct_type.members();
                symbols.get(index).map_or_else(
                    || Err(SemanticError::TooManyMembers(symbols.len(), index)),
                    |symbol| Ok(symbol.ctype.clone()),
                )
            }
            Type::Union(struct_type) => {
                if index != 0 {
                    return Err("can only initialize first member of an enum".into());
                }
                let members = struct_type.members();
                Ok(members
                    .first()
                    .map(|m| m.ctype.clone())
                    .unwrap_or(Type::Error))
            }
            Type::Error => Ok(Type::Error),
            _ => unimplemented!("type checking for aggregate initializers of type {}", self),
        }
    }
}

#[cfg(test)]
mod test {
    use super::super::test::*;
    use super::*;
    use crate::data::Locatable;
    #[test]
    fn test_initializers() {
        // scalars
        assert!(decl("int i = 3;").is_ok());

        // bounded and unbounded arrays
        let parsed = [
            decl("int a[] = {1, 2, 3};"),
            decl("int a[3] = {1, 2, 3};"),
            // possibly with trailing commas
            decl("int a[] = {1, 2, 3,};"),
            decl("int a[3] = {1, 2, 3,};"),
            // or nested
            decl("int a[][3] = {{1, 2, 3}};"),
            decl("int a[][3] = {{1, 2, 3,}};"),
            decl("int a[][3] = {{1, 2, 3,},};"),
            decl("int a[1][3] = {{1, 2, 3,},};"),
            // with misleading braces
            decl("int a[][3] = {1, 2, 3};"),
            decl("int a[][3] = {1, 2, 3,};"),
        ];
        for res in &parsed {
            match res.as_ref() {
                Ok(Declaration {
                    init: Some(Initializer::InitializerList(_)),
                    ..
                }) => {}
                Ok(other) => panic!("expected initializer list, got declaration: {}", other),
                Err(Locatable { data, .. }) => {
                    panic!("expected initializer list, got error: {}", data)
                }
            };
        }
        for err in &[
            "int i = {};",
            "int a[] = {};",
            "int i = {1, 2};",
            "int a[][3] = {{}};",
            "int a[2] = {{1, 2}};",
        ] {
            assert!(decl(err).is_err(), "{} should be an error", err);
        }
    }
    #[test]
    fn test_initializers_more() {
        assert_same("int a[][3] = {1,2,3};", "int a[][3] = {{ 1, 2, 3 }};");
        assert_same(
            "int a[][3] = {1,2,3,4};",
            "extern int a[][3] = {{ 1, 2, 3 }, { 4 } };",
        );
        //assert_same("struct { int i; float f; } s = {1, 1.2};", "struct { int i; float f; } s = {(int)1, (float)1.2};");
    }
}
