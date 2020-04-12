#![allow(dead_code)]
#![allow(unused_imports)]
#![allow(clippy::mem_replace_with_default)]

mod decl;
mod expr;
mod stmt;

use std::collections::{HashSet, VecDeque};
use std::fmt;
use std::iter::Iterator;
use std::mem;
use std::rc::Rc;

pub(crate) use crate::analyze::Analyzer;
use crate::data::*;
use crate::data::{ast::ExternalDeclaration, hir::Scope, lex::Keyword};

type Lexeme<L = Location> = CompileResult<Locatable<Token, L>, L>;
type SyntaxResult<T> = Result<T, Locatable<SyntaxError>>;

pub trait Lexer: Iterator<Item = Lexeme> {}
impl<L: Iterator<Item = Lexeme>> Lexer for L {}

#[derive(Clone, Debug)]
pub(crate) enum TagEntry {
    Struct(StructRef),
    Union(StructRef),
    // list of (name, value)s
    Enum(Vec<(InternedStr, i64)>),
}

#[derive(Clone, Debug, Default)]
struct RecursionGuard(Rc<()>);

#[derive(Debug)]
pub struct Parser<I: Lexer> {
    /// hack so that we know that `typedef int i; i j;` is legal
    pub(crate) typedefs: Scope<InternedStr, ()>,
    /// we iterate lazily over the tokens, so if we have a program that's mostly valid but
    /// breaks at the end, we don't only show lex errors
    tokens: I,
    /// VecDeque supports pop_front with reasonable efficiency
    /// this is useful because there could be multiple declarators
    /// in a single declaration; e.g. `int a, b, c;`
    pending: VecDeque<Locatable<ExternalDeclaration>>,
    /// in case we get to the end of the file and want to show an error
    last_location: Location,
    /// the last token we saw from the Lexer. None if we haven't looked ahead.
    /// Should only be used in this module.
    current: Option<Locatable<Token>>,
    /// TODO: are we sure we need 2 tokens of lookahead?
    /// this was put here for declarations, so we know the difference between
    /// int (*x) and int (int), but there's probably a workaround
    next: Option<Locatable<Token>>,
    /// whether to debug each declaration
    debug: bool,
    /// Internal API which makes it easier to return errors lazily
    error_handler: ErrorHandler,
}

impl<I: Lexer> Parser<I> {
    /// Create a new parser over the tokens.
    ///
    /// The `first` token is required for internal invariants;
    /// I would rather ensure `I` has at least one token,
    /// but I don't know a good way to do that without requiring users to
    /// use `std::iter::once`.
    pub fn new(first: Locatable<Token>, tokens: I, debug: bool) -> Self {
        Parser {
            typedefs: Default::default(),
            tokens,
            pending: Default::default(),
            last_location: first.location,
            current: Some(first),
            next: None,
            debug,
            error_handler: ErrorHandler::new(),
        }
    }
}

impl<I: Lexer> Iterator for Parser<I> {
    type Item = CompileResult<Locatable<ExternalDeclaration>>;
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
        let next = self
            .error_handler
            .pop_front()
            .map(Result::Err)
            .or_else(|| self.pending.pop_front().map(Result::Ok))
            .or_else(|| {
                // Parse more of our file

                // Remove extra semicolons
                while let Some(locatable) = self.match_next(&Token::Semicolon) {
                    self.error_handler
                        .warn("extraneous semicolon at top level", locatable.location);
                }

                // Check for end of file
                if self.peek_token().is_none() {
                    self.error_handler.pop_front().map(Err)
                } else {
                    match self.external_declaration() {
                        Ok(decls) => {
                            self.pending.push_back(decls);
                        }
                        Err(err) => {
                            // there could be semantic errors that were reported in the meantime,
                            // so we can't just return this error (it might be in the wrong order)
                            self.error_handler.push_back(err);
                        }
                    }

                    self.next()
                }
            });
        if self.debug {
            if let Some(Ok(decl)) = &next {
                println!("{}", decl.data);
            }
        }
        next
    }
}

impl<I: Lexer> Parser<I> {
    // don't use this, use next_token instead
    fn __impl_next_token(&mut self) -> Option<Locatable<Token>> {
        loop {
            match self.tokens.next() {
                Some(Ok(mut token)) => {
                    self.last_location = token.location;
                    // This is _such_ a hack
                    // I'd much rather use `Token::is_decl_specifier()` at the various places it's necessary,
                    // but that runs into limits of the lifetime system since `peek_token()` takes `&mut self`:
                    // https://doc.rust-lang.org/nomicon/lifetime-mismatch.html#limits-of-lifetimes
                    if let Token::Id(id) = token.data {
                        if self.typedefs.get(&id).is_some() {
                            token.data = Token::Keyword(Keyword::UserTypedef(id));
                        }
                    }
                    break Some(token);
                }
                Some(Err(err)) => {
                    self.last_location = err.location();
                    self.lex_error(err);
                }
                None => break None,
            }
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
            self.current = self.next.take().or_else(|| self.next_token());
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
    fn next_location(&self) -> Location {
        if let Some(token) = &self.current {
            token.location
        } else {
            self.last_location
        }
    }
    fn match_id(&mut self) -> Option<Locatable<InternedStr>> {
        if let Some(&Token::Id(id)) = self.peek_token() {
            let location = self.next_token().unwrap().location;
            Some(Locatable::new(id, location))
        } else {
            None
        }
    }
    fn match_keywords(&mut self, keywords: &[Keyword]) -> Option<Locatable<Keyword>> {
        if let Some(&Token::Keyword(keyword)) = self.peek_token() {
            for &expected in keywords {
                if keyword == expected {
                    let location = self.next_token().unwrap().location;
                    return Some(Locatable::new(keyword, location));
                }
            }
            None
        } else {
            None
        }
    }
    fn match_literal(&mut self) -> Option<Locatable<Literal>> {
        let next = self.next_token();
        if let Some(Locatable {
            data: Token::Literal(lit),
            location,
        }) = next
        {
            Some(location.with(lit))
        } else {
            self.unput(next);
            None
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
    /* error handling functions */
    fn semantic_err<S: Into<String>>(&mut self, msg: S, location: Location) {
        self.error_handler
            .push_back(CompileError::semantic(Locatable {
                location,
                data: msg.into(),
            }));
    }
    /*
     * If we're in an invalid state, try to recover.
     * Consume tokens until the end of a statement - either ';' or '}'
     */
    fn panic(&mut self) {
        while let Some(token) = self.next_token() {
            match token.data {
                Token::Semicolon => break,
                Token::RightBrace => {
                    break;
                }
                _ => continue,
            };
        }
    }
    fn expect_id(&mut self) -> SyntaxResult<Locatable<InternedStr>> {
        if let Some(id) = self.match_id() {
            Ok(id)
        } else {
            use std::borrow::Cow;

            let err = Err(Locatable {
                data: SyntaxError::ExpectedId(self.peek_token().cloned()),
                location: self.next_location(),
            });
            self.panic();
            err
        }
    }
    fn expect(&mut self, next: Token) -> SyntaxResult<Locatable<Token>> {
        let token = match self.peek_token() {
            Some(t) => t,
            None => {
                let err = Err(Locatable {
                    data: SyntaxError::from(format!("expected '{}', got '<end-of-file>'", next)),
                    // TODO: we don't actually want this, we want the end of the file
                    location: self.last_location,
                });
                self.panic();
                return err;
            }
        };
        if token.same_kind(&next) {
            Ok(self.next_token().unwrap())
        } else {
            let err = Err(Locatable {
                data: SyntaxError::from(format!("expected '{}', got '{}'", next, token)),
                location: self.next_location(),
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
    fn lex_error(&mut self, err: CompileError) {
        self.error_handler.push_back(err);
    }
    pub fn collect_results(&mut self) -> (Vec<Locatable<ExternalDeclaration>>, Vec<CompileError>) {
        let mut decls = Vec::new();
        let mut errs = Vec::new();
        for result in self {
            match result {
                Ok(decl) => decls.push(decl),
                Err(err) => errs.push(err),
            }
        }
        (decls, errs)
    }
    /// Return all warnings seen so far.
    ///
    /// These warnings are consumed and will not be returned if you call
    /// `warnings()` again.
    pub fn warnings(&mut self) -> VecDeque<CompileWarning> {
        std::mem::replace(&mut self.error_handler.warnings, Default::default())
    }
}

impl std::fmt::Display for TagEntry {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            TagEntry::Enum(_) => write!(f, "enum"),
            TagEntry::Struct(_) => write!(f, "struct"),
            TagEntry::Union(_) => write!(f, "union"),
        }
    }
}

impl Token {
    fn same_kind(&self, other: &Self) -> bool {
        match (self, other) {
            // special case keywords, assignments, and comparisons - they must match exactly
            (Token::Keyword(left), Token::Keyword(right)) => left == right,
            (Token::Assignment(left), Token::Assignment(right)) => left == right,
            (Token::Comparison(left), Token::Comparison(right)) => left == right,
            // in any other case, we're just checking they're the same enum variant
            _ => mem::discriminant(self) == mem::discriminant(other),
        }
    }
}

#[cfg(test)]
pub(crate) mod test {
    use super::Parser;
    use crate::data::ast::ExternalDeclaration;
    use crate::data::lex::test::cpp;
    use crate::data::*;
    use crate::lex::PreProcessor;
    use proptest::prelude::*;

    pub(crate) type ParseType = CompileResult<Locatable<ExternalDeclaration>>;
    pub(crate) fn parse(input: &str) -> Option<ParseType> {
        let mut all = parse_all(input);
        match all.len() {
            0 => None,
            1 => Some(all.remove(0)),
            n => Some(Err(CompileError::semantic(Locatable {
                location: match all.remove(1) {
                    Ok(x) => x.location,
                    Err(x) => x.location(),
                },
                data: format!("Expected exactly one statement, got {}", n),
            }))),
        }
    }
    #[inline]
    pub(crate) fn parse_all(input: &str) -> Vec<ParseType> {
        parser(input).collect()
    }
    pub(crate) fn parser(input: &str) -> Parser<PreProcessor> {
        //let mut lexer = Lexer::new((), format!("{}\n", input), false);
        let mut lexer = cpp(input);
        let first: Locatable<Token, Location> = lexer.next().unwrap().unwrap();
        Parser::new(first, lexer, false)
    }

    pub(crate) fn assert_same(left: &str, right: &str) {
        assert_eq!(parse_all(left), parse_all(right))
    }

    prop_compose! {
        fn arb_vec_result_locatable_token()(tokens in any::<Vec<Token>>()) -> Vec<CompileResult<Locatable<Token>>> {
            tokens.into_iter().map(|token| Ok(Locatable { data: token, location: Location::default()})).collect()
        }
    }

    proptest! {
        #[test]
        fn proptest_peek_equals_token(
            first in any::<Token>(),
            tokens in arb_vec_result_locatable_token()
            ) {
            let mut parser = Parser::new(Locatable { data: first, location: Location::default() }, tokens.into_iter(), false);

            let peek = parser.peek_token().cloned();
            let next = parser.next_token().map(|l| l.data);

            prop_assert_eq!(peek, next);
        }

        #[test]
        fn proptest_peek_next_equals_2_next_token(
            first in any::<Token>(),
            tokens in arb_vec_result_locatable_token()
            ) {
            let mut parser = Parser::new(Locatable { data: first, location: Location::default() }, tokens.into_iter(), false);

            let peek = parser.peek_next_token().cloned();
            parser.next_token();
            let next = parser.next_token().map(|l| l.data);

            prop_assert_eq!(peek, next);
        }
    }
}
