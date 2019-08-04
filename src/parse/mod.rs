mod decl;
mod expr;
mod stmt;

use std::collections::VecDeque;
use std::iter::Iterator;
use std::mem;

use crate::data::{Declaration, FunctionType, Keyword, Locatable, Location, Scope, Token};
use crate::utils::{error, warn};

type Lexeme = Locatable<Result<Token, String>>;

#[derive(Debug)]
pub struct Parser<I: Iterator<Item = Lexeme>> {
    // the variables that have been declared
    scope: Scope,
    // we iterate lazily over the tokens, so if we have a program that's mostly valid but
    // breaks at the end, we don't only show lex errors
    tokens: I,
    // VecDeque supports pop_front with reasonable efficiency
    // this is useful because errors are FIFO
    pending: VecDeque<Result<Locatable<Declaration>, Locatable<String>>>,
    // in case we get to the end of the file and want to show an error
    // TODO: are we sure this should be optional?
    last_location: Option<Location>,
    // the last token we saw from the Lexer
    current: Option<Locatable<Token>>,
    // TODO: are we sure we need 2 tokens of lookahead?
    // this was put here for declarations, so we know the difference between
    // int (*x) and int (int), but there's probably a workaround
    next: Option<Locatable<Token>>,
    // the function we are currently compiling.
    // if `None`, we are in global scope.
    // used for checking return types
    current_function: Option<FunctionData>,
}

#[derive(Debug)]
/// used to keep track of function metadata
/// while doing semantic analysis
struct FunctionData {
    /// the name of the function
    id: String,
    /// where the function was declared
    location: Location,
    /// the type of the function
    ftype: FunctionType,
    /// whether or not we've seen a return statement for this function
    seen_ret: bool,
}

impl<I> Parser<I>
where
    I: Iterator<Item = Lexeme>,
{
    pub fn new(iter: I) -> Self {
        Parser {
            scope: Default::default(),
            tokens: iter,
            pending: Default::default(),
            last_location: None,
            current: None,
            next: None,
            current_function: None,
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
        self.pending.pop_front().or_else(|| {
            while let Some(locatable) = self.match_next(&Token::Semicolon) {
                warn("extraneous semicolon at top level", &locatable.location);
            }

            // if we're at the end of the file, return None
            self.peek_token()?;

            // If declaration is None, we saw an empty specifier
            match self.declaration() {
                Err(err) => Some(Err(err)),
                Ok(Some(decl)) => Some(Ok(decl)),
                Ok(None) => self.next(),
            }
        })
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
        // NOTE: we can't just use self.current.map(|x| x.data) because of lifetimes
        match &self.current {
            Some(x) => Some(&x.data),
            None => None,
        }
    }
    // TODO: this is mostly copied from peek_token
    fn peek_next_token(&mut self) -> Option<&Token> {
        if self.next.is_none() {
            if self.current.is_none() {
                self.current = self.__impl_next_token();
            }
            self.next = self.__impl_next_token();
        }
        // NOTE: we can't just use self.current.map(|x| x.data) because of lifetimes
        match &self.next {
            Some(x) => Some(&x.data),
            None => None,
        }
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
                if *token == data {
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
    fn expect(&mut self, next: Token) -> Option<Locatable<Token>> {
        // special case keywords - they must match exactly
        if let Token::Keyword(n) = next {
            if let Some(Token::Keyword(p)) = self.peek_token() {
                if n == *p {
                    return self.next_token();
                }
            }
        }
        match self.peek_token() {
            Some(data)
                if mem::discriminant(data) == mem::discriminant(&next)
                    && mem::discriminant(data)
                        != mem::discriminant(&Token::Keyword(Keyword::Void)) =>
            {
                self.next_token()
            }
            Some(data) => {
                let message = data.to_string();
                let location = self.next_location().clone();
                // TODO: these errors don't seem to be reported?
                self.pending.push_back(Err(Locatable {
                    location,
                    data: format!("expected '{}', got '{}'", next, message),
                }));
                self.panic();
                None
            }
            None => {
                let location = self
                    .last_location
                    .as_ref()
                    .expect("parser.expect cannot be called at start of program")
                    .clone();
                self.pending.push_back(Err(Locatable {
                    location,
                    data: format!("expected '{}', got <end-of-file>", next),
                }));
                None
            }
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
        Parser::new(Lexer::new("<test suite>".to_string(), input.chars()))
    }
    #[test]
    fn peek() {
        use crate::data::{Keyword, Token};
        let mut instance = parser("int a[(int)1];");
        assert!(instance.next_token().unwrap().data == Token::Keyword(Keyword::Int));
        assert!(instance.next_token().unwrap().data == Token::Id("a".to_string()));
        assert!(instance.peek_token() == Some(&Token::LeftBracket));
        assert!(instance.peek_next_token() == Some(&Token::LeftParen));
        assert!(instance.peek_token() == Some(&Token::LeftBracket));
        assert!(instance.next_token().unwrap().data == Token::LeftBracket);
        assert!(instance.next_token().unwrap().data == Token::LeftParen);
        assert!(instance.next_token().unwrap().data == Token::Keyword(Keyword::Int));
    }
    #[test]
    fn multiple_declaration() {
        let mut decls = parse_all("int a; int a;");
        assert!(decls.len() == 2);
        assert!(decls.pop().unwrap().is_err());
        assert!(decls.pop().unwrap().is_ok());
        let mut decls = parse_all("int a; char *a[];");
        assert!(decls.len() == 2);
        assert!(decls.pop().unwrap().is_err());
        assert!(decls.pop().unwrap().is_ok());
    }
    #[test]
    fn semicolons() {
        let mut buf = Vec::new();
        buf.resize(1_000_000, ';');
        let buf: String = buf.into_iter().collect();
        assert!(parse(&buf).is_none());
    }
}
