use lazy_static::lazy_static;

use std::collections::{HashMap, VecDeque};
use std::convert::TryFrom;

use super::{Lexer, Token, SingleLocation};
use crate::data::lex::{Keyword, Literal};
use crate::data::prelude::{CompileError, Error, *};
use crate::data::error::CppError;
use crate::get_str;

pub struct PreProcessor<'a> {
    /// The preprocessor collaborates extremely closely with the lexer,
    /// since it sometimes needs to know if a token is followed by whitespace.
    lexer: Lexer<'a>,
    /// Note that this is a simple HashMap and not a Scope, because
    /// the preprocessor has no concept of scope other than `undef`
    definitions: HashMap<InternedStr, InternedStr>,
    error_handler: ErrorHandler,
    /// Whether or not to display each token as it is processed
    debug: bool,
}

type CppResult<T> = Result<Locatable<T>, CompileError>;

macro_rules! ret_err {
    ($result: expr) => {
        match $result {
            Ok(data) => data,
            Err(err) => return Some(Err(err)),
        }
    };
}

impl Iterator for PreProcessor<'_> {
    /// The preprocessor hides all internal complexity and returns only tokens.
    type Item = CppResult<Token>;
    fn next(&mut self) -> Option<Self::Item> {
        let next_token = match self.next_cpp_token()? {
            Err(err) => return Some(Err(err)),
            Ok(loc) => match loc.data {
                CppToken::Directive(directive) => self.directive(directive),
                CppToken::Token(mut token) => {
                    if let Token::Id(id) = token {
                        token = ret_err!(self.replace_id(id)?).data;
                    }
                    Self::replace_keywords(&mut token);
                    Some(Ok(Locatable::new(token, loc.location)))
                }
            },
        };
        if self.debug {
            if let Some(Ok(token)) = &next_token {
                println!("token: {}", token.data);
            }
        }
        next_token
    }
}

impl<'a> PreProcessor<'a> {
    /// Wrapper around [`Lexer::new`]
    pub fn new<T: AsRef<str> + Into<String>>(
        file: T,
        chars: std::str::Chars<'a>,
        debug: bool,
    ) -> Self {
        Self {
            lexer: Lexer::new(file, chars),
            definitions: Default::default(),
            debug,
            error_handler: Default::default(),
        }
    }
    /// Return the first valid token in the file,
    /// or None if there are no valid tokens.
    ///
    /// In either case, return all invalid tokens found.
    pub fn first_token(&mut self) -> (Option<Locatable<Token>>, VecDeque<CompileError>) {
        let mut errs = VecDeque::new();
        loop {
            match self.next() {
                Some(Ok(token)) => return (Some(token), errs),
                Some(Err(err)) => errs.push_back(err),
                None => return (None, errs),
            }
        }
    }

    /// Return all warnings found so far.
    ///
    /// These warnings are consumed and will not be returned if you call
    /// `warnings()` again.
    pub fn warnings(&mut self) -> VecDeque<CompileWarning> {
        std::mem::replace(&mut self.error_handler.warnings, Default::default())
    }

    fn add_location<T>(&self, option: Option<Result<T, CompileError>>, location: Location) -> Option<CppResult<T>> {
        Some(match option? {
            Ok(data) => Ok(Locatable::new(data, location)),
            Err(err) => Err(err),
        })
    }

    #[inline]
    fn replace_keywords(token: &mut Token) {
        if let Token::Id(name) = token {
            if let Some(keyword) = KEYWORDS.get(get_str!(name)) {
                *token = Token::Keyword(*keyword)
            }
        }
    }
    fn next_cpp_token(&mut self) -> Option<CppResult<CppToken>> {
        let next_token = self.lexer.next();
        let is_hash = match next_token {
            Some(Ok(Locatable { data: Token::Hash, .. })) => true,
            _ => false,
        };
        if is_hash && !self.lexer.seen_line_token {
            println!("saw directive start");
            let line = self.lexer.line;
            Some(match self.lexer.next()? {
                Ok(Locatable {
                    data: Token::Id(id),
                    location,
                }) => {
                    if let Ok(directive) = DirectiveKind::try_from(get_str!(id)) {
                        Ok(Locatable::new(CppToken::Directive(directive), location))
                    } else {
                        Err(Locatable::new(CppError::InvalidDirective.into(), location))
                    }
                }
                Ok(other) if self.lexer.line == line => {
                    Err(other.map(|tok| CppError::UnexpectedToken("directive", tok).into()))
                }
                other => other.map(Locatable::from),
            })
        } else {
            next_token.map(|maybe_err| maybe_err.map(Locatable::from))
        }
    }
    fn expect_id(&mut self) -> CppResult<InternedStr> {
        fn err_handler(
            value: Option<CppResult<Token>>,
            location: Location,
        ) -> CppResult<InternedStr> {
            match value {
                Some(Ok(Locatable {
                    data: Token::Id(name),
                    location,
                })) => Ok(Locatable::new(name, location)),
                Some(Err(err)) => Err(err),
                Some(Ok(other)) => Err(other.map(|tok| CppError::UnexpectedToken("identifier", tok).into())),
                None => Err(CompileError {
                    data: CppError::EndOfFile("identifier").into(),
                    location,
                }),
            }
        }
        let location = self.lexer.span(self.lexer.location.offset);
        let name = err_handler(self.lexer.next(), location)?;
        let actual = self.replace_id(name.data);
        err_handler(actual, name.location)
    }
    fn directive(&mut self, kind: DirectiveKind) -> Option<CppResult<Token>> {
        use DirectiveKind::*;
        let start = self.lexer.location.offset;
        match kind {
            If => {
                let condition = ret_err!(self.const_expr()).truthy();
                self.if_directive(condition, start)
            }
            IfDef => {
                let name = ret_err!(self.expect_id());
                self.if_directive(self.definitions.contains_key(&name.data), start)
            }
            _ => unimplemented!("preprocessing directives besides if/ifdef"),
        }
    }
    fn replace_id(&mut self, name: InternedStr) -> Option<CppResult<Token>> {
        let start = self.lexer.location.offset;
        // TODO: actually implement #define
        Some(Ok(Locatable::new(Token::Id(name), self.lexer.span(start))))
    }
    /// A C expression on a single line. Used for `#if` directives.
    ///
    /// Note that identifiers are replaced with a constant 0,
    /// as per [6.10.1](http://port70.net/~nsz/c/c11/n1570.html#6.10.1p4).
    fn const_expr(&mut self) -> Result<Literal, CompileError> {
        let mut tokens = vec![];
        let line = self.lexer.location.line;
        loop {
            self.lexer.consume_whitespace();
            if self.lexer.location.line != line {
                break;
            }
            match self.lexer.next() {
                Some(Ok(token @ Locatable { data: Token::Id(_), .. })) => {
                    tokens.push(Ok(token.map(|_| Token::Literal(Literal::Int(0)))));
                }
                Some(token) => tokens.push(token),
                None => return Err(CompileError::new(
                    Error::UnterminatedDirective("#if"),
                    self.lexer.location,
                )),
            };
        }
        let mut parser = crate::Parser::new(tokens.into_iter(), self.debug)?;
        Ok(parser.expr()?.constexpr().unwrap().data.0)
    }
    fn if_directive(&mut self, condition: bool, start: u32) -> Option<CppResult<Token>> {
        if condition {
            unimplemented!()
        } else {
            ret_err!(self.consume_if_directive(start));
            self.next()
        }
    }
    /// Assuming we've just seen `#if 0`, keep consuming tokens until `#endif`
    /// This has to take into account nesting of #if directives.
    ///
    /// Example:
    /// ```c
    /// # if 0
    /// # if 1
    ///   int main() {}
    /// # endif
    /// void f() {}
    /// # endif
    /// int g() { return 0; }
    /// ```
    /// should yield `int` as the next token, not `void`.
    fn consume_if_directive(&mut self, start: u32) -> Result<(), CompileError> {
        fn match_directive(token: &CppResult<CppToken>, expected: DirectiveKind) -> bool {
            match token {
                Ok(Locatable {
                    data: CppToken::Directive(directive),
                    ..
                }) => *directive == expected,
                _ => false,
            }
        }
        let mut depth = 1;
        while dbg!(depth) > 0 {
            println!("in loop");
            let token = match dbg!(self.next_cpp_token()) {
                Some(token) => token,
                None => {
                    return Err(Locatable::new(
                        CppError::UnterminatedDirective("#if or #ifdef"),
                        self.lexer.span(start),
                    )
                    .into())
                }
            };
            if match_directive(&token, DirectiveKind::If)
                || match_directive(&token, DirectiveKind::IfDef)
            {
                depth += 1;
            } else if match_directive(&token, DirectiveKind::EndIf) {
                depth -= 1;
            }
        }
        Ok(())
    }
}

impl Literal {
    fn truthy(&self) -> bool {
        unimplemented!()
    }
}

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
enum DirectiveKind {
    If,
    EndIf,
    Else,
    IfDef,
    Include,
    Define,
    Undef,
    Line,
    Error,
    Pragma,
}

#[derive(Clone, Debug, PartialEq)]
enum CppToken {
    Token(Token),
    Directive(DirectiveKind),
}

impl From<Locatable<Token>> for Locatable<CppToken> {
    fn from(token: Locatable<Token>) -> Locatable<CppToken> {
        Locatable::new(CppToken::Token(token.data), token.location)
    }
}

impl TryFrom<&str> for DirectiveKind {
    type Error = ();
    fn try_from(s: &str) -> Result<Self, ()> {
        use DirectiveKind::*;
        Ok(match s {
            "if" => If,
            "endif" => EndIf,
            "else" => Else,
            "ifdef" => IfDef,
            "include" => Include,
            "define" => Define,
            "undef" => Undef,
            "line" => Line,
            "error" => Error,
            "pragma" => Pragma,
            _ => return Err(()),
        })
    }
}

lazy_static! {
    static ref KEYWORDS: HashMap<&'static str, Keyword> = map!{
        // control flow
        "if" => Keyword::If,
        "else" => Keyword::Else,
        "do" => Keyword::Do,
        "while" => Keyword::While,
        "for" => Keyword::For,
        "switch" => Keyword::Switch,
        "case" => Keyword::Case,
        "default" => Keyword::Default,
        "break" => Keyword::Break,
        "continue" => Keyword::Continue,
        "return" => Keyword::Return,
        "goto" => Keyword::Goto,

        // types
        "va_list" => Keyword::VaList,
        "__builtin_va_list" => Keyword::VaList,
        "_Bool" => Keyword::Bool,
        "char" => Keyword::Char,
        "short" => Keyword::Short,
        "int" => Keyword::Int,
        "long" => Keyword::Long,
        "float" => Keyword::Float,
        "double" => Keyword::Double,
        "_Complex" => Keyword::Complex,
        "_Imaginary" => Keyword::Imaginary,
        "void" => Keyword::Void,
        "signed" => Keyword::Signed,
        "unsigned" => Keyword::Unsigned,
        "typedef" => Keyword::Typedef,
        "enum" => Keyword::Enum,
        "union" => Keyword::Union,
        "struct" => Keyword::Struct,

        // qualifiers
        "const" => Keyword::Const,
        "volatile" => Keyword::Volatile,
        "restrict" => Keyword::Restrict,
        "_Atomic" => Keyword::Atomic,
        "_Thread_local" => Keyword::ThreadLocal,

        // function qualifiers
        "inline" => Keyword::Inline,
        "_Noreturn" => Keyword::NoReturn,

        // storage classes
        "auto" => Keyword::Auto,
        "register" => Keyword::Register,
        "static" => Keyword::Static,
        "extern" => Keyword::Extern,

        // compiler intrinsics
        "sizeof" => Keyword::Sizeof,
        "_Alignof" => Keyword::Alignof,
        "_Alignas" => Keyword::Alignas,
        "_Generic" => Keyword::Generic,
        "_Static_assert" => Keyword::StaticAssert,
    };
}

#[cfg(test)]
mod tests {
    use super::{CppResult, Keyword, PreProcessor, KEYWORDS};
    use crate::data::prelude::*;
    fn cpp(input: &str) -> PreProcessor {
        PreProcessor::new("<test suite>", input.chars(), false)
    }
    fn assert_keyword(token: Option<CppResult<Token>>, expected: Keyword) {
        match token {
            Some(Ok(Locatable {
                data: Token::Keyword(actual),
                ..
            })) => assert_eq!(actual, expected),
            _ => panic!("not a keyword: {:?}", token),
        }
    }
    #[test]
    fn keywords() {
        for keyword in KEYWORDS.values() {
            println!("{}", keyword);
            assert_keyword(cpp(&keyword.to_string()).next(), *keyword);
        }
    }
    #[test]
    fn ifdef() {
        let code = "#ifdef a
        whatever, doesn't matter
        #endif";
        assert_eq!(cpp(code).next(), None);
        let code = "#ifdef a\n#endif";
        assert_eq!(cpp(code).next(), None);
        assert!(cpp("#ifdef").next().unwrap().is_err());
        let nested = "#ifdef a
        #ifdef b
        int main() {}
        #endif
        #endif
        char;";
        assert_eq!(
            cpp(nested).next().unwrap().unwrap().data,
            Token::Keyword(Keyword::Char)
        );
    }
}
