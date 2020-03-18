use super::*;
use crate::data::ast::{Declaration, DeclarationSpecifier, Declarator, Expr, TypeName};
use std::convert::{TryFrom, TryInto};

#[derive(Debug)]
enum InternalDeclaratorType {
    Id(InternedStr),
    Pointer { qualifiers: Vec<DeclarationSpecifier> },
    Array { size: Option<Box<Expr>> },
    // TODO: support abstract parameters
    Function { params: Vec<(TypeName, InternedStr)>, varargs: bool },
}

#[derive(Debug)]
struct InternalDeclarator {
    current: InternalDeclaratorType,
    next: Option<Box<InternalDeclarator>>,
}

impl<I: Iterator<Item = Lexeme>> Parser<I> {
    pub fn declaration(&mut self) -> SyntaxResult<Locatable<Declaration>> {
        unimplemented!()
    }
    // expects to be followed by a ')'
    pub fn type_name(&mut self) -> SyntaxResult<Locatable<TypeName>> {
        let specifiers = self.specifiers()?;
        let fold = |all_locs: Option<Location>, spec: &Locatable<_>| {
            all_locs.map_or(Some(spec.location), |existing| {
                Some(existing.merge(spec.location))
            })
        };
        let specifier_locations = specifiers.iter().fold(None, fold);
        let specifiers: Vec<_> = specifiers.into_iter().map(|s| s.data).collect();
        if self.peek_token() == Some(&Token::RightParen) {
            return if specifiers.is_empty() {
                Err(self.next_location().with(SyntaxError::ExpectedType))
            } else {
                use crate::data::ast::DeclaratorType;

                let location = specifier_locations.expect("just checked >= 1 specifier");
                Ok(location.with(TypeName {
                    specifiers,
                    declarator: Declarator { id: None, decl: DeclaratorType::End },
                }))
            };
        }
        let declarator = self.declarator(true)?
            .expect("types should have a declarator or syntax error if not followed by ')'")
            .map(InternalDeclarator::parse_declarator);
        let location =
            specifier_locations.map_or(declarator.location, |loc| loc.merge(declarator.location));
        let type_name = TypeName {
            specifiers,
            declarator: declarator.data,
        };
        Ok(Locatable::new(type_name, location))
    }
    fn specifiers(&mut self) -> SyntaxResult<Vec<Locatable<DeclarationSpecifier>>> {
        let mut specifiers = Vec::new();
        while let Some(&Token::Keyword(keyword)) = self.peek_token() {
            let spec = match keyword {
                Keyword::Struct | Keyword::Union => self.struct_specifier()?,
                Keyword::Enum => self.enum_specifier()?,
                other if !other.is_decl_specifier() => {
                    let err = SyntaxError::ExpectedDeclSpecifier(keyword);
                    let location = self.next_token().unwrap().location;
                    return Err(location.with(err));
                }
                _ => {
                    let location = self.next_token().unwrap().location;
                    Locatable::new(keyword.try_into().unwrap(), location)
                }
            };
            specifiers.push(spec);
        }
        Ok(specifiers)
    }
    fn struct_specifier(&mut self) -> SyntaxResult<Locatable<DeclarationSpecifier>> {
        unimplemented!("struct/union specifiers");
    }
    fn enum_specifier(&mut self) -> SyntaxResult<Locatable<DeclarationSpecifier>> {
        unimplemented!("enum specifiers");
    }
    fn merge_decls(current: Locatable<InternalDeclaratorType>, next: Option<Locatable<InternalDeclarator>>) -> Locatable<InternalDeclarator> {
        if let Some(next) = next {
            let location = current.location.merge(next.location);
            let decl = InternalDeclarator {
                current: current.data,
                next: Some(Box::new(next.data)),
            };
            Locatable::new(decl, location)
        } else {
            current.map(|data| InternalDeclarator {
                current: data,
                next: None,
            })
        }
    }
    fn declarator(&mut self, allow_abstract: bool) -> SyntaxResult<Option<Locatable<InternalDeclarator>>> {
        let mut pointer_decls = Vec::new();
        // NOTE: outdated comment
        // decls coming earlier in the Vec have lower precedence than the ones coming later
        // e.g. `*const *volatile p` would look like `vec![Pointer(const), Pointer(volatile), Id("p")]`
        // and  `*const (*f)()` would look like `vec![Pointer(const), Function, Pointer, Id("f")]`
        // anything to the left of a `Function` represents the return type
        // anything to the right represents a declarator with higher precedence
        // the `Id` should always be the last declarator in the Vec
        while let Some(Locatable { mut location, .. }) = self.match_next(&Token::Star) {
            let mut qualifiers = Vec::new();
            // *const volatile p
            while let Some(Locatable {
                location: keyword_loc,
                data: Token::Keyword(keyword),
            }) = self.match_any(&[
                &Token::Keyword(Keyword::Const),
                &Token::Keyword(Keyword::Volatile),
                &Token::Keyword(Keyword::Restrict),
                &Token::Keyword(Keyword::Atomic),
                &Token::Keyword(Keyword::ThreadLocal),
            ]) {
                location = location.merge(keyword_loc);
                qualifiers.push(keyword.try_into().unwrap());
            }
            let current = Locatable::new(InternalDeclaratorType::Pointer{ qualifiers }, location);
            pointer_decls.push(current);
        }
        // TODO: allow abstract declarators
        let mut decl = self.direct_declarator(allow_abstract)?;
        while let Some(pointer) = pointer_decls.pop() {
            decl = Some(Self::merge_decls(pointer, decl));
        }
        Ok(dbg!(decl))
    }
    /*
     * Originally written as follows:
     * direct_declarator
     *  : identifier
     *  | '(' declarator ')'
     *  | direct_declarator '[' ']'
     *  | direct_declarator '[' constant_expr ']'
     *  | direct_declarator '(' ')'
     *  | direct_declarator '(' parameter_type_list ')'
     *  ;
     *
     * Additionally, we combine abstract_declarators, because most of the code is the same.
     * direct_abstract_declarator
     *  : '(' abstract_declarator ')'
     *  | '[' ']'
     *  | '[' constant_expr ']'
     *  | direct_abstract_declarator '[' ']'
     *  | direct_abstract_declarator '[' constant_expr ']'
     *  | '(' ')'
     *  | '(' parameter_type_list ')'
     *  | direct_abstract_declarator '(' ')'
     *  | direct_abstract_declarator '(' parameter_type_list ')'
     *  ;
     *
     * Because we can't handle left-recursion, we rewrite it as follows:
     * direct_abstract_declarator
     *   | identifier postfix_type*
     *   : '(' abstract_declarator ')' postfix_type*
     *   | postfix_type*  /* only for abstract_declarators */
     *   ;
     *
     * postfix_type:
     *   : '[' ']'
     *   | '[' constant_expr ']'
     *   | '(' ')'
     *   | '(' parameter_type_list ')'
     *   ;
     *
     *   How do we tell abstract_declarator and parameter_type_list apart?
     *   parameter_type_list starts with declaration specifiers, abstract_declarator doesn't:
     *   https://stackoverflow.com/questions/56410673/how-should-int-fint-be-parsed
     */
    fn direct_declarator(
        &mut self,
        allow_abstract: bool,
    ) -> SyntaxResult<Option<Locatable<InternalDeclarator>>> {
        // we'll pass this to postfix_type in just a second
        // if None, we didn't find an ID
        // should only happen if allow_abstract is true
        let decl: Option<Locatable<InternalDeclarator>> = match self.peek_token() {
            Some(Token::Id(_)) => {
                Some(self.next_token().unwrap().map(|data| {
                    match data {
                        Token::Id(id) => InternalDeclarator {
                            current: InternalDeclaratorType::Id(id),
                            next: None,
                        },
                        _ => panic!("peek() should always return the same thing as next()"),
                    }
                }))
            }
            // handled by postfix_type
            Some(Token::LeftBracket) if allow_abstract => None,
            Some(Token::LeftParen) => {
                // this is the reason we need to save next - otherwise we
                // consume LeftParen without postfix_type ever seeing it
                match self.peek_next_token() {
                    // parameter_type_list, leave it for postfix_type
                    // need to check allow_abstract because we haven't seen an ID at
                    // this point
                    Some(Token::Keyword(k)) if k.is_decl_specifier() && allow_abstract => None,
                    // abstract_declarator - could be an error,
                    // but if so we'll catch it later
                    _ => {
                        // the one we already matched
                        self.expect(Token::LeftParen)
                            .expect("peek_next_token should be accurate");
                        let declarator = self.declarator(allow_abstract)?;
                        self.expect(Token::RightParen)?;
                        declarator
                    }
                }
            }
            _ if allow_abstract => None,
            Some(x) => {
                let err = Err(Locatable::new(
                    SyntaxError::from(format!("expected variable name or '(', got '{}'", x)),
                    self.next_location(),
                ));
                self.panic();
                return err;
            }
            None => {
                return Err(self.next_location().with(SyntaxError::from(
                    "expected variable name or '(', got <end-of-of-file>",
                )));
            }
        };
        self.postfix_type(decl, allow_abstract)
    }
    /*
     * not in original reference, see comments to `direct_declarator`
     *
     * rewritten grammar:
     *   postfix_type:
     *        '[' ']'
     *      | '[' constant_expr ']'
     *      | '(' ')'
     *      | '(' parameter_type_list ')'
     *      | /* empty */
     *      ;
     */
    fn postfix_type(
        &mut self,
        mut prefix: Option<Locatable<InternalDeclarator>>,
        allow_abstract: bool,
    ) -> SyntaxResult<Option<Locatable<InternalDeclarator>>> {
        // postfix
        while let Some(data) = self.peek_token() {
            let current = match data {
                // Array; Specified in section 6.7.6.2 of the C11 spec
                Token::LeftBracket => {
                    self.expect(Token::LeftBracket).unwrap();
                    let (size, location) = if let Some(token) = self.match_next(&Token::RightBracket) {
                        (None, token.location)
                    } else {
                        let expr = Box::new(self.expr()?);
                        (Some(expr), self.expect(Token::RightBracket)?.location)
                    };
                    Locatable::new(InternalDeclaratorType::Array { size }, location)
                }
                Token::LeftParen => self.parameter_type_list()?,
                _ => break
            };
            prefix = Some(Self::merge_decls(current, prefix))
        }
        Ok(prefix)
    }
    /*
     * function parameters
     * reference grammar:
     *
     *  parameter_type_list:
     *        parameter_list
     *      | parameter_list ',' ELLIPSIS
     *      ;
     *
     *  parameter_list:
     *        parameter_declaration
     *      | parameter_list ',' parameter_declaration
     *      ;
     *
     *  parameter_declaration:
     *        declaration_specifiers declarator
     *      | declaration_specifiers
     *      | declaration_specifiers abstract_declarator
     *      ;
     *
     */
     fn parameter_type_list(&mut self) -> SyntaxResult<Locatable<InternalDeclaratorType>> {
        let left_paren = self.expect(Token::LeftParen)
            .expect("parameter_type_list should only be called with '(' as the next token")
            .location;
        let mut params = vec![];
        if let Some(right_paren) = self.match_next(&Token::RightParen) {
            return Ok(Locatable::new(InternalDeclaratorType::Function {
                params,
                varargs: false,
            }, left_paren.merge(right_paren.location)));
        }
        loop {
            if self.match_next(&Token::Ellipsis).is_some() {
                let right_paren = self.expect(Token::RightParen)?.location;
                return Ok(Locatable::new(InternalDeclaratorType::Function {
                    params,
                    varargs: true,
                }, left_paren.merge(right_paren)));
            }
            let param = self.type_name()?;
            //unimplemented!("parameters");
            /*
            let (sc, quals, param_type, _) = self.declaration_specifiers()?;
            // true: allow abstract_declarators
            let declarator = self.declarator(true, quals)?;
            */
            // int f(void, int);
            /*
            if let Some(decl) = declarator {
                let (id, mut ctype) = decl
                    .parse_type(param_type, false, &self.last_location)
                    .recover(&mut self.error_handler);
                // int f(int a[]) is the same as int f(int *a)
                // TODO: parse int f(int a[static 5])
                if let Type::Array(to, _) = ctype {
                    ctype = Type::Pointer(to);
                }
                // I will probably regret this in the future
                // default() for String is "",
                // which can never be passed in by the lexer
                // this also makes checking if the parameter is abstract or not easy to check
                let Locatable { location, data } = id.unwrap_or(Locatable {
                    location: self.next_location(),
                    data: Default::default(),
                });
                if data != Default::default() && params.iter().any(|p| p.data.id == data) {
                    self.semantic_err(
                        format!(
                            "duplicate parameter name '{}' in function declaration",
                            data,
                        ),
                        location,
                    );
                }
                params.push(Locatable {
                    location,
                    data: Symbol {
                        id: data,
                        ctype,
                        qualifiers: quals,
                        storage_class: StorageClass::Auto,
                        init: true,
                    },
                });
            // int f(int, void);
            } else if param_type == Type::Void && !params.is_empty() {
                self.error_handler.push_back(
                    self.last_location
                        .error(SemanticError::InvalidVoidParameter),
                );
            } else {
                // abstract param
                params.push(Locatable {
                    location: self.last_location,
                    data: Symbol {
                        id: Default::default(),
                        ctype: param_type,
                        qualifiers: quals,
                        storage_class: StorageClass::Auto,
                        init: true,
                    },
                });
            }
            */
            // lol this is so broken
            params.push((param.data, InternedStr::default()));
            if self.match_next(&Token::Comma).is_none() {
                let right_paren = self.expect(Token::RightParen)?.location;
                let location = left_paren.merge(right_paren);
                return Ok(Locatable::new(InternalDeclaratorType::Function {
                    params,
                    varargs: false,
                }, location));
            }
        }
    }
}

impl InternalDeclarator {
    fn parse_declarator(self) -> Declarator {
        use crate::data::ast::DeclaratorType;
        use InternalDeclaratorType::*;

        fn get_id(mut declarator: &InternalDeclarator) -> InternedStr {
            loop {
                match declarator.current {
                    InternalDeclaratorType::Id(id) => return id,
                    _ => declarator = declarator.next.as_ref().expect("abstract params not supported"),
                }
            }
        }
        let mut id = None;
        let mut current = DeclaratorType::End;
        //let mut current = Declarator::End;
        //let current = self.current;
        let mut declarator = Some(self);
        while let Some(decl) = declarator {
            current = match decl.current {
                Id(i) => {
                    id = Some(i);
                    current //Declarator::Id { id, next: Box::new(current) },
                }
                Pointer { qualifiers } => DeclaratorType::Pointer { to: Box::new(current), qualifiers },
                Array { size } => DeclaratorType::Array { of: Box::new(current), size },
                Function{ params, varargs } => DeclaratorType::Function {
                    return_type: Box::new(current),
                    params,
                    varargs,
                },
            };
            declarator = decl.next.map(|x| *x);
        }
        Declarator { decl: current, id }
    }
}

impl TryFrom<Keyword> for DeclarationSpecifier {
    type Error = ();
    #[rustfmt::skip]
    fn try_from(k: Keyword) -> Result<DeclarationSpecifier, ()> {
        use DeclarationSpecifier::*;
        use Keyword::*;

        /*
        if let Ok(t) = TypeSpecifier::try_from(k) {
            return Ok(DeclarationSpecifier::Type(t));
        }
        */

        // TODO: get rid of this macro and store a `enum Keyword { Qualifier(Qualifier), etc. }` instead
        macro_rules! change_enum {
            ($val: expr, $source: path, $dest: ident, $($name: ident),* $(,)?) => {
                match $val {
                    $(<$source>::$name => Ok($dest::$name),)*
                    _ => Err(()),
                }
            }
        }
        change_enum!(k, Keyword, DeclarationSpecifier,
            Const, Volatile, Restrict, Atomic, ThreadLocal,
            Unsigned, Signed,
            Bool, Char, Short, Int, Long, Float, Double, Void,
            Complex, Imaginary, VaList,
            Extern,
        )
        /*
        macro_rules! change_enum {
            ( $($name: ident),* ) => {
                    $(Keyword::$name => Ok(DeclarationSpecifier::$name),)*
            }
        }
        */
        /*
        match k {
            // type specifier
            //Unsigned | Signed | Bool | Char | Short | Int | Long | Float | Double | Void
            // complex type specifier
            //Struct | Union | Enum | VaList | Complex | Imaginary
            // storage class
            Keyword::Extern => DeclarationSpecifier::Extern,
            Keyword::Static => DeclarationSpecifier::Static,
            Keyword::Auto => DeclarationSpecifier::Auto,
            Keyword::Register => DeclarationSpecifier::Register,
            Keyword::Typedef => DeclarationSpecifier::Typedef,
            Keyword::Const => DeclarationSpecifier::Const,
            Keyword::Static => DeclarationSpecifier::Static,
            //change_enum!(Extern, Static)
            | Keyword::Auto | Keyword::Register | Keyword::Typedef
            // qualifier
            | Keyword::Const | Keyword::Volatile | Keyword::Restrict | Keyword::Atomic | Keyword::ThreadLocal
            // function qualifier
            | Inline | NoReturn => true,
            _ => false,
            Keyword::Const => DeclarationSpecifier::Const,
        }
        */
        //*/
    }
}

impl Token {
    pub(super) fn is_decl_specifier(&self) -> bool {
        match self {
            Token::Keyword(k) => k.is_decl_specifier(),
            //Token::Id(id) => id.is_typedef(),
            _ => false,
        }
    }
}

impl Keyword {
    pub(super) fn is_decl_specifier(self) -> bool {
        use Keyword::*;
        match self {
            // type specifier
            Unsigned | Signed | Bool | Char | Short | Int | Long | Float | Double | Void
            // complex type specifier
            | Struct | Union | Enum | VaList | Complex | Imaginary
            // storage class
            | Extern | Static | Auto | Register | Typedef
            // qualifier
            | Const | Volatile | Restrict | Atomic | ThreadLocal
            // function qualifier
            | Inline | NoReturn => true,
            _ => false,
        }
    }
}
