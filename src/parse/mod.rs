mod decl;
mod stmt;

use std::collections::VecDeque;
use std::iter::Iterator;
use std::mem;

use crate::data::{Keyword, Locatable, Location, Stmt, Token};
use crate::utils::error;

type Lexeme = Locatable<Result<Token, String>>;

#[derive(Debug)]
pub struct Parser<I: Iterator<Item = Lexeme>> {
    // we iterate lazily over the tokens, so if we have a program that's mostly valid but
    // breaks at the end, we don't only show lex errors
    tokens: I,
    // VecDeque supports pop_front with reasonable efficiency
    // this is useful because errors are FIFO
    pending: VecDeque<Result<Locatable<Stmt>, Locatable<String>>>,
    // in case we get to the end of the file and want to show an error
    // TODO: are we sure this should be optional?
    last_location: Option<Location>,
    // the last token we saw from the Lexer
    current: Option<Locatable<Token>>,
    // TODO: are we sure we need 2 tokens of lookahead?
    // this was put here for declarations, so we know the difference between
    // int (*x) and int (int), but there's probably a workaround
    next: Option<Locatable<Token>>,
}

impl<I> Parser<I>
where
    I: Iterator<Item = Lexeme>,
{
    pub fn new(iter: I) -> Self {
        Parser {
            tokens: iter,
            pending: Default::default(),
            last_location: None,
            current: None,
            next: None,
        }
    }
}

impl<I: Iterator<Item = Lexeme>> Iterator for Parser<I> {
    type Item = Result<Locatable<Stmt>, Locatable<String>>;
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
            let Locatable {
                data: lexed,
                location,
            } = self.next_token()?;
            match lexed {
                // NOTE: we do not allow implicit int
                // https://stackoverflow.com/questions/11064292
                Token::Keyword(t) if t.is_decl_specifier() => self.declaration(t),
                _ => Some(Err(Locatable {
                    data: "not handled".to_string(),
                    location,
                })),
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
            None
        } else {
            None
        }
    }
    /* WARNING: may panic
     * only use if you are SURE token is a keyword
     */
    fn expect_keyword(token: Token) -> Keyword {
        match token {
            Token::Keyword(k) => k,
            _ => panic!("peek should never be different from next"),
        }
    }
    fn expect(&mut self, next: Token) -> (bool, &Location) {
        match self.peek_token() {
            Some(data) if mem::discriminant(&next) == mem::discriminant(data) => {
                self.next_token();
                (
                    true,
                    self.last_location
                        .as_ref()
                        .expect("last_location should be set whenever next_token is called"),
                )
            }
            Some(data) => {
                let message = data.to_string();
                let location = self.next_location().clone();
                self.pending.push_back(Err(Locatable {
                    location,
                    data: format!("expected '{}', got '{}'", next, message),
                }));
                (false, self.next_location())
            }
            None => {
                let location = self
                    .last_location
                    .as_ref()
                    .expect("parser.expect cannot be called at start of program");
                self.pending.push_back(Err(Locatable {
                    location: location.clone(),
                    data: format!("expected '{}', got <end-of-file>", next),
                }));
                (false, location)
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
    use crate::data::{Locatable, Stmt};
    use crate::lex::Lexer;

    pub type ParseType = Result<Locatable<Stmt>, Locatable<String>>;
    pub fn parse(input: &str) -> Option<ParseType> {
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
    pub fn parse_all(input: &str) -> Vec<ParseType> {
        parser(input).collect()
    }
    #[inline]
    pub fn match_data<T>(lexed: Option<ParseType>, closure: T) -> bool
    where
        T: Fn(Stmt) -> bool,
    {
        match lexed {
            Some(Ok(stmt)) => closure(stmt.data),
            _ => false,
        }
    }
    #[inline]
    pub fn match_all<I, T>(mut lexed: I, closure: T) -> bool
    where
        I: Iterator<Item = ParseType>,
        T: Fn(Stmt) -> bool,
    {
        lexed.all(|l| match l {
            Ok(stmt) => closure(stmt.data),
            _ => false,
        })
    }
    #[inline]
    fn parser(input: &str) -> Parser<Lexer> {
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
}
