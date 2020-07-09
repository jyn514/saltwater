pub(crate) mod decl;
mod expr;
mod stmt;

use std::collections::VecDeque;
use std::iter::Iterator;
use std::mem;

use crate::data::*;
use crate::data::{ast::ExternalDeclaration, hir::Scope, lex::Keyword};
use crate::RecursionGuard;

type Lexeme = CompileResult<Locatable<Token>>;
type SyntaxResult<T> = Result<T, Locatable<SyntaxError>>;

/// Trait alias for Iterator, but stable
pub trait Lexer: Iterator<Item = Lexeme> {}
impl<I: Iterator<Item = Lexeme>> Lexer for I {}

#[derive(Debug)]
pub struct Parser<I: Lexer> {
    /// hack so that we know that `typedef int i; i j;` is legal
    pub(crate) typedefs: Scope<InternedStr, ()>,
    /// we iterate lazily over the tokens, so if we have a program that's mostly valid but
    /// breaks at the end, we don't only show lex errors
    tokens: std::iter::Peekable<I>,
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
    /// Internal API which prevents segfaults due to stack overflow
    recursion_guard: RecursionGuard,
}

impl<I: Lexer> Parser<I> {
    /// Create a new parser over the tokens.
    pub fn new(tokens: I, debug: bool) -> Self {
        Parser {
            typedefs: Default::default(),
            tokens: tokens.peekable(),
            pending: Default::default(),
            // The only time this is used is when an error occurs,
            // which only happens after at least one token has been seen.
            // So this default location will never be used.
            last_location: Location::default(),
            current: None,
            next: None,
            debug,
            error_handler: ErrorHandler::new(),
            recursion_guard: Default::default(),
        }
    }
    /// Return whether this parser has fully finished parsing.
    ///
    /// This can be used if, for example, you call `parser.expr()`
    /// and want to see if there are any left-over tokens.
    pub fn is_empty(&mut self) -> bool {
        self.peek_token().is_none()
    }
}

impl<I: Lexer> Iterator for Parser<I> {
    type Item = CompileResult<Locatable<ExternalDeclaration>>;
    /// ```yacc
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
    /// ```
    /// <http://www.quut.com/c/ANSI-C-grammar-y.html#translation_unit>
    fn next(&mut self) -> Option<Self::Item> {
        loop {
            // check for pending changes from the last declaration
            if let Some(err) = self.error_handler.pop_front() {
                return Some(Err(err));
            } else if let Some(decl) = self.pending.pop_front() {
                if self.debug {
                    println!("ast: {}", decl.data);
                }
                return Some(Ok(decl));
            }

            // Check for end of file
            if self.peek_token().is_none() {
                // peek_token can encounter lex errors that it doesn't return
                return self.error_handler.pop_front().map(Err);
            }

            // Remove extra semicolons
            while let Some(locatable) = self.match_next(&Token::Semicolon) {
                self.error_handler
                    .warn("extraneous semicolon at top level", locatable.location);
            }

            // Parse more of our file
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
        }
    }
}

impl<I: Lexer> Parser<I> {
    fn recursion_check(&mut self) -> RecursionGuard {
        self.recursion_guard
            .recursion_check(&mut self.error_handler)
    }
    // don't use this, use next_token instead
    fn __impl_next_token(&mut self) -> Option<Locatable<Token>> {
        loop {
            match self.tokens.next() {
                Some(Ok(Locatable {
                    data: Token::Whitespace(_),
                    ..
                })) => continue,
                Some(Ok(Locatable {
                    data: Token::Literal(LiteralToken::Str(mut concat_strs, mut concat_len)),
                    mut location,
                })) => {
                    // 5.1.1.2p1: Translation phase 6: Adjacent string literal tokens are concatenated.
                    loop {
                        match self.tokens.peek() {
                            Some(Ok(Locatable {
                                data: Token::Literal(LiteralToken::Str(merge_strs, merge_len)),
                                location: next_location,
                            })) => {
                                location = location.merge(next_location);
                                concat_strs.append(&mut merge_strs.clone());
                                concat_len += merge_len - 1; // -1 for removed null terminator
                                self.tokens.next(); // Actually remove next
                            }
                            Some(Ok(Locatable {
                                data: Token::Whitespace(_),
                                ..
                            })) => {
                                self.tokens.next();
                            }
                            Some(Ok(_)) => break,
                            Some(Err(_)) => {
                                let err = self.tokens.next().unwrap().unwrap_err();
                                self.error_handler.push_back(err);
                            }
                            None => break,
                        }
                    }
                    break Some(Locatable::new(
                        Token::Literal(LiteralToken::Str(concat_strs, concat_len)),
                        location,
                    ));
                }
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
            let tmp = mem::take(&mut self.next);
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
        match self.peek_token() {
            Some(&Token::Id(name)) | Some(&Token::Keyword(Keyword::UserTypedef(name))) => {
                let location = self.next_token().unwrap().location;
                Some(Locatable::new(name, location))
            }
            _ => None,
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
    fn match_literal(&mut self) -> Option<Locatable<LiteralToken>> {
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
    /// - replace `self.current` with `item`
    /// - replace `self.next` with `self.current`
    /// - the previous value of `self.next` is lost
    fn unput(&mut self, item: Option<Locatable<Token>>) {
        assert!(self.next.is_none());
        self.next = mem::replace(&mut self.current, item);
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
        std::mem::take(&mut self.error_handler.warnings)
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

    #[inline]
    pub(crate) fn parse_all(input: &str) -> Vec<ParseType> {
        parser(input).collect()
    }
    pub(crate) fn parser(input: &str) -> Parser<PreProcessor> {
        Parser::new(cpp(input), false)
    }

    prop_compose! {
        fn arb_vec_result_locatable_token()(tokens in any::<Vec<Token>>()) -> Vec<CompileResult<Locatable<Token>>> {
            tokens.into_iter().map(|token| Ok(Locatable { data: token, location: Location::default()})).collect()
        }
    }

    proptest! {
        #[test]
        fn proptest_peek_equals_token(
            tokens in arb_vec_result_locatable_token()
        ) {
            let mut parser = Parser::new(tokens.into_iter(), false);

            let peek = parser.peek_token().cloned();
            let next = parser.next_token().map(|l| l.data);

            prop_assert_eq!(peek, next);
        }

        #[test]
        fn proptest_peek_next_equals_2_next_token(
            tokens in arb_vec_result_locatable_token()
        ) {
            let mut parser = Parser::new(tokens.into_iter(), false);

            let peek = parser.peek_next_token().cloned();
            parser.next_token();
            let next = parser.next_token().map(|l| l.data);

            prop_assert_eq!(peek, next);
        }
    }

    #[test]
    fn test_strings() {
        let assert_str = |s, expected: &str| {
            use crate::data::ast::ExprType;
            use crate::parse::expr::test::expr;

            let e = expr(s).unwrap();
            let mut bytes = match e.data {
                ExprType::Literal(LiteralValue::Str(s)) => s,
                x => panic!("wrong expression: {:?}", x),
            };
            assert_eq!(bytes.pop(), Some(b'\0'));
            assert_eq!(std::str::from_utf8(&bytes).unwrap(), expected);
        };
        assert_str("\"this is a sample string\"", "this is a sample string");
        assert_str("\"consecutive \" \"strings\"", "consecutive strings");
        assert_str("\"string with \\0\"", "string with \0");
        // regression test for https://github.com/jyn514/rcc/issues/350
        let newlines = " \"a\" \n \"b\" ";
        assert_str(newlines, "ab");
    }
}
