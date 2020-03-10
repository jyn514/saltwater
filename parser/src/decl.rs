use super::*;
use crate::data::ast::{Declaration, TypeName};

impl<I: Iterator<Item = Lexeme>> Parser<I> {
    pub fn declaration(&mut self) -> SyntaxResult<Locatable<Declaration>> {
        unimplemented!()
    }
    pub fn type_name(&mut self) -> SyntaxResult<Locatable<TypeName>> {
        /*
        let mut specifiers = Vec::new();
        while let Some(Token::Keyword(keyword)) = self.peek_token() {
            if !keyword.is_decl_specifier() {
                let err = SyntaxError::ExpectedDeclSpecifier(keyword.data);
                return Err(keyword.location.with(err));
            }
        }
        */
        unimplemented!("type_name")
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
