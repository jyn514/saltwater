use super::*;
use crate::data::ast::{Declaration, DeclarationSpecifier, Declarator, TypeName};
use std::convert::{TryFrom, TryInto};

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
                let location = specifier_locations.expect("just checked >= 1 specifier");
                Ok(location.with(TypeName {
                    specifiers,
                    declarator: None,
                }))
            };
        }
        let declarator = self.declarator()?;
        let location =
            specifier_locations.map_or(declarator.location, |loc| loc.merge(declarator.location));
        let type_name = TypeName {
            specifiers,
            declarator: Some(declarator.data),
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
    fn declarator(&mut self) -> SyntaxResult<Locatable<Declarator>> {
        let mut pointers = Vec::new();
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
            pointers.push(Locatable::new(qualifiers, location));
        }
        let Locatable {
            data: mut decl,
            mut location,
        } = self.direct_declarator()?;
        for pointer in pointers.into_iter().rev() {
            decl = Declarator::Pointer {
                to: Box::new(decl),
                qualifiers: pointer.data,
            };
            location = pointer.location.merge(location);
        }
        Ok(Locatable::new(decl, location))
    }
    fn direct_declarator(&mut self) -> SyntaxResult<Locatable<Declarator>> {
        let next = match self.next_token() {
            Some(x) => x,
            None => {
                return Err(Locatable::new(
                    SyntaxError::EndOfFile("direct declarator"),
                    self.last_location,
                ))
            }
        };
        match next.data {
            Token::Id(id) => Ok(Locatable::new(Declarator::Id(id), next.location)),
            // []
            Token::LeftBracket => {
                let (size, location) = if let Some(right) = self.match_next(&Token::RightBracket) {
                    (None, next.location.merge(right.location))
                } else {
                    let expr = self.expr()?;
                    let right_loc = self.expect(Token::RightBracket)?.location;
                    let loc = next.location.merge(expr.location).merge(right_loc);
                    (Some(Box::new(expr)), loc)
                };
                let decl = Declarator::Array {
                    of: unimplemented!("need to rewrite this"),
                    size,
                };
                Ok(Locatable::new(decl, location))
            }
            Token::LeftParen => {
                // if the next token is a pointer, id, or `(`, it must be a parenthesized declarator
                // e.g. (*), (p)
                // otherwise, assume it's a function declaration
                // this allows such horrors as `int f(());` and `int f((()))`.
                let inner = match self.peek_token() {
                    Some(Token::Star) | Some(Token::Id(_)) | Some(Token::LeftParen) => {
                        self.declarator()
                    }
                    // NOTE: parameter_type_list returns a declarator, not just a list of params
                    _ => self.parameter_type_list(),
                }?;
                let right_loc = self.expect(Token::RightParen)?.location;
                let loc = next.location.merge(inner.location).merge(right_loc);
                Ok(Locatable::new(inner.data, loc))
            }
            other => Err(Locatable::new(
                SyntaxError::ExpectedDeclarator(other),
                next.location,
            )),
        }
    }
    fn parameter_type_list(&mut self) -> SyntaxResult<Locatable<Declarator>> {
        unimplemented!("function declarations")
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
