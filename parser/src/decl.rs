use super::*;
use crate::data::ast::{
    self, Declaration, DeclarationSpecifier, Declarator, Expr, ExternalDeclaration, Initializer,
    TypeName,
};
use crate::data::lex::LocationTrait;
use std::convert::{TryFrom, TryInto};

#[derive(Debug)]
enum InternalDeclaratorType {
    Id(InternedStr),
    Pointer {
        qualifiers: Vec<DeclarationSpecifier>,
    },
    Array {
        size: Option<Box<Expr>>,
    },
    // TODO: support abstract parameters
    Function {
        params: Vec<(TypeName, InternedStr)>,
        varargs: bool,
    },
}

#[derive(Debug)]
struct InternalDeclarator {
    current: InternalDeclaratorType,
    next: Option<Box<InternalDeclarator>>,
}

impl<I: Iterator<Item = Lexeme>> Parser<I> {
    /// external_declaration
    /// : function_definition
    /// | declaration
    /// ;
    ///
    /// declaration
    /// : declaration_specifiers ';'
    /// | declaration_specifiers init_declarator_list ';'
    /// ;
    pub fn external_declaration(&mut self) -> SyntaxResult<Locatable<ExternalDeclaration>> {
        let (specifiers, specifier_locations) = self.specifiers()?;
        // TODO: allow `int;`
        let declarator = self.init_declarator()?;
        let mut location = declarator.location.maybe_merge(specifier_locations);

        //if let Some(token) = self.match_next(&Token::LeftBrace) {
        if self.peek_token() == Some(&Token::LeftBrace) {
            if !declarator.data.declarator.is_function() {
                return Err(location.with(SyntaxError::NotAFunction(declarator.data)));
            } else if let Some(init) = declarator.data.init {
                return Err(location.with(SyntaxError::FunctionInitializer(init)));
            }
            let ctype = TypeName {
                specifiers,
                declarator: declarator.data.declarator,
            };
            return self.function_body(Locatable::new(ctype, location));
        }
        let mut decls = vec![declarator];
        while self.match_next(&Token::Semicolon).is_none() {
            self.expect(Token::Comma)?;
            let decl = self.init_declarator()?;
            location = location.merge(decl.location);
            decls.push(decl);
        }
        let declaration = Declaration {
            specifiers,
            declarators: decls,
        };
        Ok(Locatable::new(
            ExternalDeclaration::Declaration(declaration),
            location,
        ))
    }
    // expects to be followed by a ')'
    pub fn type_name(&mut self) -> SyntaxResult<Locatable<TypeName>> {
        let (specifiers, specifier_locations) = self.specifiers()?;
        if self.peek_token() == Some(&Token::RightParen) {
            return if specifiers.is_empty() {
                Err(self.next_location().with(SyntaxError::ExpectedType))
            } else {
                use crate::data::ast::DeclaratorType;

                let location = specifier_locations.expect("just checked >= 1 specifier");
                Ok(location.with(TypeName {
                    specifiers,
                    declarator: Declarator {
                        id: None,
                        decl: DeclaratorType::End,
                    },
                }))
            };
        }
        let declarator = self
            .declarator(true)?
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
    fn specifiers(&mut self) -> SyntaxResult<(Vec<DeclarationSpecifier>, Option<Location>)> {
        let mut specifiers = Vec::new();
        let mut all_locs = None;
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
            all_locs = all_locs.map_or(Some(spec.location), |existing: Location| {
                Some(existing.merge(spec.location))
            });
            specifiers.push(spec.data);
        }
        Ok((specifiers, all_locs))
    }
    fn struct_specifier(&mut self) -> SyntaxResult<Locatable<DeclarationSpecifier>> {
        unimplemented!("struct/union specifiers");
    }
    fn enum_specifier(&mut self) -> SyntaxResult<Locatable<DeclarationSpecifier>> {
        unimplemented!("enum specifiers");
    }

    fn init_declarator(&mut self) -> SyntaxResult<Locatable<ast::InitDeclarator>> {
        let decl = self.declarator(false)?;
        let init = if self.match_next(&Token::EQUAL).is_some() {
            Some(self.initializer()?)
        } else {
            None
        };
        // TODO: this is wrong
        let location = self.last_location;
        let decl = decl.ok_or_else(|| location.with(SyntaxError::ExpectedDeclarator))?;
        Ok(decl.map(|d| ast::InitDeclarator {
            declarator: InternalDeclarator::parse_declarator(d),
            init,
        }))
    }

    fn function_body(
        &mut self, func: Locatable<TypeName>,
    ) -> SyntaxResult<Locatable<ExternalDeclaration>> {
        use crate::data::ast::FunctionDefinition;

        let body = self.compound_statement()?;
        let location = func.location.merge(body.location);
        let def = FunctionDefinition {
            body: body.data,
            specifiers: func.data.specifiers,
            declarator: func.data.declarator,
        };
        Ok(Locatable::new(ExternalDeclaration::Function(def), location))
    }

    fn merge_decls(
        current: Locatable<InternalDeclaratorType>, next: Option<Locatable<InternalDeclarator>>,
    ) -> Locatable<InternalDeclarator> {
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
    fn declarator(
        &mut self, allow_abstract: bool,
    ) -> SyntaxResult<Option<Locatable<InternalDeclarator>>> {
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
            let current = Locatable::new(InternalDeclaratorType::Pointer { qualifiers }, location);
            pointer_decls.push(current);
        }
        // TODO: allow abstract declarators
        let mut decl = self.direct_declarator(allow_abstract)?;
        while let Some(pointer) = pointer_decls.pop() {
            decl = Some(Self::merge_decls(pointer, decl));
        }
        Ok(decl)
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
        &mut self, allow_abstract: bool,
    ) -> SyntaxResult<Option<Locatable<InternalDeclarator>>> {
        // we'll pass this to postfix_type in just a second
        // if None, we didn't find an ID
        // should only happen if allow_abstract is true
        let decl: Option<Locatable<InternalDeclarator>> = match self.peek_token() {
            Some(Token::Id(_)) => Some(self.next_token().unwrap().map(|data| match data {
                Token::Id(id) => InternalDeclarator {
                    current: InternalDeclaratorType::Id(id),
                    next: None,
                },
                _ => panic!("peek() should always return the same thing as next()"),
            })),
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
        self.postfix_type(decl)
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
    #[inline]
    fn postfix_type(
        &mut self, mut prefix: Option<Locatable<InternalDeclarator>>,
    ) -> SyntaxResult<Option<Locatable<InternalDeclarator>>> {
        while let Some(data) = self.peek_token() {
            let current = match data {
                // Array; Specified in section 6.7.6.2 of the C11 spec
                Token::LeftBracket => {
                    self.expect(Token::LeftBracket).unwrap();
                    let (size, location) =
                        if let Some(token) = self.match_next(&Token::RightBracket) {
                            (None, token.location)
                        } else {
                            let expr = Box::new(self.expr()?);
                            (Some(expr), self.expect(Token::RightBracket)?.location)
                        };
                    Locatable::new(InternalDeclaratorType::Array { size }, location)
                }
                Token::LeftParen => self.parameter_type_list()?,
                _ => break,
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
        let left_paren = self
            .expect(Token::LeftParen)
            .expect("parameter_type_list should only be called with '(' as the next token")
            .location;
        let mut params = vec![];
        if let Some(right_paren) = self.match_next(&Token::RightParen) {
            return Ok(Locatable::new(
                InternalDeclaratorType::Function {
                    params,
                    varargs: false,
                },
                left_paren.merge(right_paren.location),
            ));
        }
        loop {
            if self.match_next(&Token::Ellipsis).is_some() {
                let right_paren = self.expect(Token::RightParen)?.location;
                return Ok(Locatable::new(
                    InternalDeclaratorType::Function {
                        params,
                        varargs: true,
                    },
                    left_paren.merge(right_paren),
                ));
            }
            let param = self.type_name()?;
            // lol this is so broken
            params.push((param.data, InternedStr::default()));
            if self.match_next(&Token::Comma).is_none() {
                let right_paren = self.expect(Token::RightParen)?.location;
                let location = left_paren.merge(right_paren);
                return Ok(Locatable::new(
                    InternalDeclaratorType::Function {
                        params,
                        varargs: false,
                    },
                    location,
                ));
            }
        }
    }
    fn initializer(&mut self) -> SyntaxResult<Initializer> {
        // initializer_list
        if self.match_next(&Token::LeftBrace).is_some() {
            let ret = self.aggregate_initializer();
            self.expect(Token::RightBrace)?;
            return ret;
        }
        let expr = self.assignment_expr()?;
        Ok(Initializer::Scalar(Box::new(expr)))
    }

    // handle char[][3] = {{1,2,3}}, but also = {1,2,3} and {{1}, 2, 3}
    // NOTE: this does NOT consume {} except for sub-elements
    fn aggregate_initializer(&mut self) -> SyntaxResult<Initializer> {
        let mut elems = vec![];
        while self.match_next(&Token::RightBrace).is_none() {
            let next = if self.match_next(&Token::LeftBrace).is_some() {
                let t = self.aggregate_initializer()?;
                self.expect(Token::RightBrace)?;
                t
            } else {
                // scalar
                self.initializer()?
            };
            elems.push(next);
            // NOTE: this allows trailing commas
            if self.match_next(&Token::Comma).is_none() {
                self.expect(Token::RightBrace)?;
                break;
            };
        }
        Ok(Initializer::Aggregate(elems))
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
                    _ => {
                        declarator = declarator
                            .next
                            .as_ref()
                            .expect("should have been caught earlier")
                    }
                }
            }
        }
        let mut id = None;
        let mut current = DeclaratorType::End;
        let mut declarator = Some(self);
        while let Some(decl) = declarator {
            current = match decl.current {
                Id(i) => {
                    id = Some(i);
                    current
                }
                Pointer { qualifiers } => DeclaratorType::Pointer {
                    to: Box::new(current),
                    qualifiers,
                },
                Array { size } => DeclaratorType::Array {
                    of: Box::new(current),
                    size,
                },
                Function { params, varargs } => DeclaratorType::Function {
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
