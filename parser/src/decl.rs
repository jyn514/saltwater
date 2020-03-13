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
        unimplemented!("declarator")
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
