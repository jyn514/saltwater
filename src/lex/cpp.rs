use lazy_static::lazy_static;

use std::collections::{HashMap, VecDeque};

use super::{Lexer, Token, SingleLocation};
use crate::data::lex::{Keyword, Literal};
use crate::data::prelude::{CompileError as Error, *};
use crate::get_str;

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

pub struct PreProcessor<'a> {
    /// The preprocessor collaborates extremely closely with the lexer,
    /// since it sometimes needs to know if a token is followed by whitespace.
    lexer: Lexer<'a>,
    /// Note that this is a simple HashMap and not a Scope, because
    /// the preprocessor has no concept of scope other than `undef`
    definitions: HashMap<InternedStr, InternedStr>,
    error_handler: ErrorHandler,
}

type CppResult<T> = Result<Locatable<T>, Error>;

impl Iterator for PreProcessor<'_> {
    /// The preprocessor hides all internal complexity and returns only tokens.
    type Item = CppResult<Token>;
    fn next(&mut self) -> Option<Self::Item> {
        let next_token = self.lexer.next();
        if let Some(Ok(loc)) = next_token {
            match loc.data {
                Token::Hash if !self.lexer.seen_line_token => {
                    let current_line = self.lexer.line;
                    self.lexer.consume_whitespace();
                    // see if we had '#' alone on a line
                    if current_line != self.lexer.line {
                        None
                    } else {
                        let start = self.lexer.location.offset;
                        let directive = self.directive();
                        self.add_location(directive, self.lexer.span(start))
                    }
                }
                Token::Id(id) => {
                    let stream = self.replace_id(id);
                    self.add_location(stream, loc.location)
                }
                _ => Some(Ok(loc)),
            }
        } else {
            next_token
        }
    }
}

macro_rules! ret_err {
    ($result: expr) => {
        match $result {
            Ok(data) => data,
            Err(err) => return Some(Err(err)),
        }
    };
}

impl<'a> PreProcessor<'a> {
    /// Wrapper around [`Lexer::new`]
    pub fn new<T: AsRef<str> + Into<String>>(
        file: T,
        chars: std::str::Chars<'a>,
        debug: bool,
    ) -> Self {
        Self {
            lexer: Lexer::new(file, chars, debug),
            definitions: Default::default(),
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

    fn add_location<T>(&self, option: Option<Result<T, Error>>, location: Location) -> Option<CppResult<T>> {
        Some(match option? {
            Ok(data) => Ok(Locatable::new(data, location)),
            Err(err) => Err(err),
        })
    }

    fn expect_id(&mut self) -> CppResult<InternedStr> {
        const ERR: &str = "preprocessor: expected identifier, got ";
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
                Some(Ok(other)) => Err(Error::from(Locatable::new(
                    format!("{}{}", ERR, other.data),
                    other.location,
                ))),
                None => Err(Error::from(Locatable::new(
                    format!("{}{}", ERR, "<end-of-file>"),
                    location,
                ))),
            }
        }
        let location = self.lexer.span(self.lexer.location.offset);
        let name = err_handler(self.lexer.next(), location)?;
        let actual = self
            .replace_id(name.data)
            .map(|maybe_err| maybe_err.map(|data| Locatable::new(data, name.location)));
        err_handler(actual, name.location)
    }
    fn directive(&mut self) -> Option<Result<Token, Error>> {
        let id = ret_err!(self.expect_id());
        match get_str!(id.data) {
            "if" => {
                let condition = ret_err!(self.const_expr()).truthy();
                self.if_directive(condition)
            }
            "ifdef" => {
                let name = ret_err!(self.expect_id());
                self.if_directive(self.definitions.contains_key(&name.data))
            }
            "include" | "define" | "undef" | "line" | "error" | "pragma" => {
                unimplemented!("preprocessing directives besides if/ifdef")
            }
            _ => Some(Err(CompileError::new(
                SemanticError::Generic("invalid preprocessing directive".into()).into(),
                id.location,
            ))),
        }
    }
    fn replace_id(&mut self, name: InternedStr) -> Option<Result<Token, Error>> {
        // TODO: actually implement #define
        Some(match KEYWORDS.get(get_str!(name)) {
            Some(keyword) => Ok(Token::Keyword(*keyword)),
            None => Ok(Token::Id(name)),
        })
    }
    fn const_expr(&mut self) -> Result<Literal, Error> {
        unimplemented!("constant expressions")
    }
    fn if_directive(&mut self, _condition: bool) -> Option<Result<Token, Error>> {
        unimplemented!("if/ifdef")
    }
}

impl Literal {
    fn truthy(&self) -> bool {
        unimplemented!()
    }
}
