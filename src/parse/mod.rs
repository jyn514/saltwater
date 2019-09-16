mod decl;
mod expr;
mod stmt;

use std::collections::VecDeque;
use std::iter::Iterator;
use std::mem;

use crate::data::{prelude::*, Scope};
use crate::utils::{error, warn};

type Lexeme = Locatable<Result<Token, String>>;

#[derive(Clone, Debug)]
enum TagEntry {
    Struct(Vec<Symbol>),
    Union(Vec<Symbol>),
    // list of (name, value)s
    Enum(Vec<(String, i64)>),
}

#[derive(Debug)]
pub struct Parser<I: Iterator<Item = Lexeme>> {
    /// the variables that have been declared
    scope: Scope<String, Symbol>,
    /// the compound types that have been declared (struct/union/enum)
    tag_scope: Scope<String, TagEntry>,
    /// we iterate lazily over the tokens, so if we have a program that's mostly valid but
    /// breaks at the end, we don't only show lex errors
    tokens: I,
    /// VecDeque supports pop_front with reasonable efficiency
    /// this is useful because errors are FIFO
    pending: VecDeque<Result<Locatable<Declaration>, Locatable<String>>>,
    /// in case we get to the end of the file and want to show an error
    /// TODO: are we sure this should be optional?
    last_location: Option<Location>,
    /// the last token we saw from the Lexer
    current: Option<Locatable<Token>>,
    /// TODO: are we sure we need 2 tokens of lookahead?
    /// this was put here for declarations, so we know the difference between
    /// int (*x) and int (int), but there's probably a workaround
    next: Option<Locatable<Token>>,
    /// the function we are currently compiling.
    /// if `None`, we are in global scope.
    /// used for checking return types
    current_function: Option<FunctionData>,
    /// whether to debug each declaration
    debug: bool,
}

#[derive(Debug)]
/// used to keep track of function metadata
/// while doing semantic analysis
struct FunctionData {
    /// the name of the function
    id: String,
    /// where the function was declared
    location: Location,
    /// the return type of the function
    return_type: Type,
}

impl<I> Parser<I>
where
    I: Iterator<Item = Lexeme>,
{
    pub fn new(iter: I, debug: bool) -> Self {
        Parser {
            scope: Scope::new(),
            tag_scope: Scope::new(),
            tokens: iter,
            pending: Default::default(),
            last_location: None,
            current: None,
            next: None,
            current_function: None,
            debug,
        }
    }
}

impl<I: Iterator<Item = Lexeme>> Iterator for Parser<I> {
    type Item = Result<Locatable<Declaration>, Locatable<String>>;
    /// translation_unit
    /// : external_declaration
    /// | translation_unit external_declaration
    /// ;
    ///
    /// external_declaration
    /// : function_definition
    /// | declaration
    /// ;
    ///
    /// function_definition
    /// : declarator compound_statement
    /// | declaration_specifiers declarator compound_statement
    /// ;
    fn next(&mut self) -> Option<Self::Item> {
        let next = self.pending.pop_front().or_else(|| {
            while let Some(locatable) = self.match_next(&Token::Semicolon) {
                warn("extraneous semicolon at top level", &locatable.location);
            }

            // if we're at the end of the file, return None
            self.peek_token()?;
            let mut decls = match self.declaration() {
                Ok(decls) => decls,
                Err(err) => return Some(Err(err)),
            };
            let next = match decls.pop_front() {
                Some(decl) => decl,
                None => return self.next(),
            };
            self.pending.extend(decls.into_iter().map(Result::Ok));
            Some(Ok(next))
        });
        if self.debug {
            match &next {
                Some(Ok(decl)) => println!("declaration: {:#?}", decl.data),
                Some(Err(err)) => println!("error: {:#?}", err.data),
                None => {}
            }
        }
        next
    }
}

impl<I: Iterator<Item = Lexeme>> Parser<I> {
    /* utility functions */
    // don't use this, use next_token instead
    fn __impl_next_token(&mut self) -> Option<Locatable<Token>> {
        match self.tokens.next() {
            Some(x) => match x.data {
                Ok(token) => {
                    self.last_location = Some(x.location.clone());
                    Some(Locatable {
                        location: x.location,
                        data: token,
                    })
                }
                Err(err) => {
                    error(&err, &x.location);
                    self.last_location = Some(x.location);
                    self.__impl_next_token()
                }
            },
            None => None,
        }
    }
    fn next_token(&mut self) -> Option<Locatable<Token>> {
        if self.current.is_some() {
            let tmp = mem::replace(&mut self.next, None);
            mem::replace(&mut self.current, tmp)
        } else {
            self.__impl_next_token()
        }
    }
    fn peek_token(&mut self) -> Option<&Token> {
        if self.current.is_none() {
            self.current = mem::replace(&mut self.next, None).or_else(|| self.next_token());
        }
        self.current.as_ref().map(|x| &x.data)
    }
    // TODO: this is mostly copied from peek_token
    fn peek_next_token(&mut self) -> Option<&Token> {
        if self.next.is_none() {
            if self.current.is_none() {
                self.current = self.__impl_next_token();
            }
            self.next = self.__impl_next_token();
        }
        self.next.as_ref().map(|x| &x.data)
    }
    fn next_location(&mut self) -> &Location {
        if self.peek_token().is_some() {
            &self.current.as_ref().unwrap().location
        } else {
            self.last_location
                .as_ref()
                .expect("can't call next_location on an empty file")
        }
    }
    fn match_next(&mut self, next: &Token) -> Option<Locatable<Token>> {
        self.match_any(&[next])
    }
    fn match_any(&mut self, choices: &[&Token]) -> Option<Locatable<Token>> {
        if let Some(data) = self.peek_token() {
            for token in choices {
                if token.same_kind(data) {
                    return self.next_token();
                }
            }
        }
        None
    }
    /*
     * If we're in an invalid state, try to recover.
     * Consume tokens until the end of a statement - either ';' or '}'
     */
    fn panic(&mut self) {
        loop {
            match self.peek_token() {
                None | Some(Token::Semicolon) | Some(Token::RightBrace) => break,
                _ => self.next_token(),
            };
        }
    }
    fn expect(&mut self, next: Token) -> Result<Locatable<Token>, Locatable<String>> {
        let token = match self.peek_token() {
            Some(t) => t,
            None => {
                let err = Err(Locatable {
                    location: self.next_location().clone(),
                    data: format!("expected '{}', got '<end-of-file>'", next),
                });
                self.panic();
                return err;
            }
        };
        if token.same_kind(&next) {
            Ok(self.next_token().unwrap())
        } else {
            let err = Err(Locatable {
                data: format!("expected '{}', got '{}'", next, token),
                location: self.next_location().clone(),
            });
            self.panic();
            err
        }
    }
    /// replace `self.current` with `item`
    /// replace `self.next` with `self.current`
    /// the previous value of `self.next` is lost
    fn unput(&mut self, item: Option<Locatable<Token>>) {
        let tmp = mem::replace(&mut self.current, item);
        mem::replace(&mut self.next, tmp);
    }
}

impl Token {
    fn same_kind(&self, other: &Self) -> bool {
        // special case keywords - they must match exactly
        if let (Token::Keyword(left), Token::Keyword(right)) = (self, other) {
            return left == right;
        }
        mem::discriminant(self) == mem::discriminant(other)
    }
}

#[cfg(test)]
mod tests {
    use super::Parser;
    use crate::data::{Declaration, Locatable};
    use crate::lex::Lexer;

    pub(crate) type ParseType = Result<Locatable<Declaration>, Locatable<String>>;
    pub(crate) fn parse(input: &str) -> Option<ParseType> {
        let mut all = parse_all(input);
        match all.len() {
            0 => None,
            1 => Some(all.remove(0)),
            n => Some(Err(Locatable {
                location: match all.remove(1) {
                    Ok(x) => x.location,
                    Err(x) => x.location,
                },
                data: format!("Expected exactly one statement, got {}", n),
            })),
        }
    }
    #[inline]
    pub(crate) fn parse_all(input: &str) -> Vec<ParseType> {
        parser(input).collect()
    }
    #[inline]
    pub(crate) fn match_data<T>(lexed: Option<ParseType>, closure: T) -> bool
    where
        T: Fn(Declaration) -> bool,
    {
        match lexed {
            Some(Ok(decl)) => closure(decl.data),
            _ => false,
        }
    }
    #[inline]
    pub(crate) fn match_all<I, T>(mut lexed: I, closure: T) -> bool
    where
        I: Iterator<Item = ParseType>,
        T: Fn(Declaration) -> bool,
    {
        lexed.all(|l| match l {
            Ok(decl) => closure(decl.data),
            _ => false,
        })
    }
    #[inline]
    pub(crate) fn parser(input: &str) -> Parser<Lexer> {
        let lex = Lexer::new("<test suite>".to_string(), input.chars(), false);
        Parser::new(lex, false)
    }
    #[test]
    fn peek() {
        use crate::data::{Keyword, Token};
        let mut instance = parser("int a[(int)1];");
        assert_eq!(
            instance.next_token().unwrap().data,
            Token::Keyword(Keyword::Int)
        );
        assert_eq!(
            instance.next_token().unwrap().data,
            Token::Id("a".to_string())
        );
        assert_eq!(instance.peek_token(), Some(&Token::LeftBracket));
        assert_eq!(instance.peek_next_token(), Some(&Token::LeftParen));
        assert_eq!(instance.peek_token(), Some(&Token::LeftBracket));
        assert_eq!(instance.next_token().unwrap().data, Token::LeftBracket);
        assert_eq!(instance.next_token().unwrap().data, Token::LeftParen);
        assert_eq!(
            instance.next_token().unwrap().data,
            Token::Keyword(Keyword::Int)
        );
    }
    #[test]
    fn multiple_declaration() {
        let mut decls = parse_all("int a; int a;");
        assert_eq!(decls.len(), 2);
        assert!(decls.pop().unwrap().is_ok());
        assert!(decls.pop().unwrap().is_ok());
        let mut decls = parse_all("int a; char *a[];");
        assert_eq!(decls.len(), 2);
        assert!(decls.pop().unwrap().is_err());
        assert!(decls.pop().unwrap().is_ok());
    }
    #[test]
    fn semicolons() {
        let mut buf = Vec::new();
        buf.resize(10_000, ';');
        let buf: String = buf.into_iter().collect();
        assert!(parse(&buf).is_none());
    }
}
