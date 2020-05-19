#![allow(unreachable_pub)]
//! Macro replacement
//!
//! This module does no parsing and accepts only tokens.

use crate::{
    error::CppError, CompileError, CompileResult, InternedStr, Locatable, Location, Token,
};
use super::cpp::CppResult;
use std::collections::{HashMap, HashSet, VecDeque};
use std::iter::Peekable;

pub struct MacroReplacer <I: Iterator<Item = CppResult<Token>>> {
    /// The ids seen while replacing the current token.
    ///
    /// This allows cycle detection. It should be reset after every replacement list
    /// - _not_ after every token, since otherwise that won't catch some mutual recursion
    /// See https://github.com/jyn514/rcc/issues/427 for examples.
    ids_seen: HashSet<InternedStr>,
    /// Note that this is a simple HashMap and not a Scope, because
    /// the preprocessor has no concept of scope other than `undef`
    pub definitions: HashMap<InternedStr, Definition>,
    /// The token stream to read from
    pub(crate) inner: Peekable<I>,
    /*
    /// The replacement list for a single token
    pending: VecDeque<Locatable<Token>>,
    /// The location for the current replacement list
    ///
    /// This is the location of the call site, not the definition site.
    last_location: Option<Location>,
    */
}

/*
// TODO: I don't think this is necessary? we can use `ids_seen` instead
#[derive(Clone)]
pub enum PendingToken {
    Replacement(Token),
    Cyclic(Token),
}

impl PendingToken {
    pub(super) fn token(&self) -> &Token {
        match self {
            PendingToken::Replacement(t) => t,
            PendingToken::Cyclic(t) => t,
        }
    }
    fn as_tuple(self) -> (Token, bool) {
        match self {
            PendingToken::Replacement(t) => (t, true),
            PendingToken::Cyclic(t) => (t, false),
        }
    }
}

impl From<Token> for PendingToken {
    fn from(token: Token) -> Self {
        PendingToken::Replacement(token)
    }
}
*/

#[derive(Debug)]
pub enum Definition {
    Object(Vec<Token>),
    Function {
        params: Vec<InternedStr>,
        body: Vec<Token>,
    },
}

/*
impl<I: Iterator<Item = CppResult<Token>>> Iterator for MacroReplacer<I> {
    type Item = CppResult<Token>;
    fn next(&mut self) -> Option<Self::Item> {
        loop {
            // We have two things we need to handle.
            // First, we could have gotten to the end of the file;
            // Second, the current token could be an identifier that was `#define`d to an empty token list.
            // This loop is for the second case, not the first.
            let (replacement, location) = if let Some(token) = self.pending.pop_front() {
                return Some(Ok(token));
            } else {
                // Since there are no tokens in `self.pending`, we must not be in the middle of replacing a macro.
                self.ids_seen.clear();
                // `inner` does not perform macro replacement,
                // so if it returns None we got to EOF.
                match self.inner.next()? {
                    Err(err) => return Some(Err(err)),
                    Ok(t) => (self.replace(t.data), t.location),
                }
            };
            let replacement = replacement.into_iter();
            if let Some(token) = replacement.next() {
                self.pending = replacement.map(|t| Locatable::new(t, location)).collect();
                return Some(Ok(Locatable::new(token, location)));
            }
            // This token was an empty define, so continue looking for tokens
        }
    }
}
*/

impl<I: Iterator<Item = CppResult<Token>>> MacroReplacer<I> {
    pub fn new(tokens: I) -> Self {
        Self {
            inner: tokens.peekable(),
            definitions: Default::default(),
            ids_seen: Default::default(),
            //pending: Default::default(),
            //last_location: None,
        }
    }

    pub fn with_definitions(tokens: I, definitions: HashMap<InternedStr, Definition>,) -> Self {
        Self {
            definitions,
            ..Self::new(tokens)
        }
    }

    /*
    /// This function must be called after a single replacement list has finished being processed.
    pub(super) fn finished_replacement(&mut self) {
        self.ids_seen.clear();
    }
    */

    /// Possibly recursively replace tokens.
    ///
    /// This first performs object-macro replacement, then function-macro replacement.
    /// For example, consider this C program:
    /// ```c
    /// #define f(a, b) a + b
    /// #define g f
    /// #define c d
    /// g(c, 1)
    /// ```
    /// First, the name of the function will be replaced: `f(c, 1)`.
    /// Next, all arguments are replaced: `f(d, 1)`.
    /// Finally, function-macros are replaced: `d + 1`.
    ///
    /// If at any point there is a cyclic replacement, no error is generated.
    /// Instead, replacement immediately stops for the current token.
    /// However, future tokens may still be replaced. For example, take
    /// ```c
    /// #define b c
    /// #define f(a) g(a + 1)
    /// #define g(a) f(a)
    /// f(b)
    /// ```
    /// The cycle f -> g will be detected after the first time through: `f(b)` -> `g(b + 1)` -> `f(b + 1)`.
    /// Then, replacements of later tokens occur: `f(c + 1)`.
    ///
    /// Note that known cycles do not persist between calls to `replace`.
    /// This means that very long cycles will be recalculated on each call.
    // TODO: if you call replace() the wrong way, could you induce infinite recursion somehow?
    // It doesn't seem so ... but the call to `ids_seen.clear()` makes me nervous.
    pub fn replace(
        &mut self,
        token: Token,
        location: Location,
    ) -> Vec<CompileResult<Locatable<Token>>> {
        let mut replacements = Vec::new();
        let mut pending = VecDeque::new();
        //assert!(self.pending.is_empty());
        pending.push_back(location.with(token));
        //let mut tokens = vec_deque![token];

        // outer loop: replace all tokens in the replacement list
        while let Some(token) = pending.pop_front() {
            // first step: perform (recursive) substitution on the ID
            if let Token::Id(id) = token.data {
                if !self.ids_seen.contains(&id) {
                    match self.definitions.get(&id) {
                        Some(Definition::Object(replacement_list)) => {
                            self.ids_seen.insert(id);
                            // prepend the new tokens to the pending tokens
                            // They need to go before, not after. For instance:
                            // ```c
                            // #define a b c d
                            // #define b 1 + 2
                            // a
                            // ```
                            // should replace to `1 + 2 c d`, not `c d 1 + 2`
                            let mut new_pending = VecDeque::new();
                            // we need a `clone()` because `self.definitions` needs to keep its copy of the definition
                            new_pending
                                .extend(replacement_list.iter().cloned().map(|t| location.with(t)));
                            new_pending.append(&mut pending);
                            pending = new_pending;
                            //self.replace_object(replacement_list),
                            continue;
                        }
                        Some(Definition::Function { params, body }) => {
                            self.ids_seen.insert(id);
                            self.replace_function(params, body, location, &mut pending);
                            continue;
                        }
                        None => {}
                    }
                    /*
                    // TODO: so many allocations :(
                    let mut obj_replacements = self.replace_object(id);
                    // second step: perform function macro replacement
                    if let Some(Token::Id(name)) = obj_replacements.pop_front() {
                        for token in self.replace_function(name, location) {
                            match token {
                                Ok(t) => self.pending
                                Err(err) => replacements.push(Err(err)),
                            }
                        }
                        self.pending.extend(func);
                    }
                    self.pending.extend(obj_replacements.into_iter().map(Ok));
                    continue;
                    */
                }
            }
            replacements.push(Ok(token));
        }

        // Since there are no tokens in `self.pending`, we have finished replacing this macro.
        self.ids_seen.clear();
        replacements
    }

    /*
    /// Recursively replace the current identifier with its definitions.
    ///
    /// This does cycle detection by replacing the repeating identifier at least once;
    /// see the `recursive_macros` test for more details.
    // TODO: this needs to have an idea of 'pending chars', not just pending tokens
    fn replace_object(&mut self, name: InternedStr) -> VecDeque<Token> {
        let mut pending = VecDeque::new();
        if let Some(Definition::Object(def)) = self.definitions.get(&name) {
            self.ids_seen.insert(name);
            // prepend the new tokens to the pending tokens
            // They need to go before, not after. For instance:
            // ```c
            // #define a b c d
            // #define b 1 + 2
            // a
            // ```
            // should replace to `1 + 2 c d`, not `c d 1 + 2`
            let mut new_pending = VecDeque::new();
            new_pending.extend(def.iter().map(|token| {
                // we need a `clone()` because `self.definitions` needs to keep its copy of the definition
                token.clone()
            }));
            new_pending.append(&mut pending);
            pending = new_pending;
        } else {
            pending.push_back(Token::Id(name));
        }
        pending
        //self.replace_function(name, start)
    }
    */

    // TODO: this should probably return Result<VecDeque, CompileError> instead
    pub fn replace_function(
        &self,
        params: &[InternedStr],
        body: &[Token],
        location: Location,
        incoming: &mut VecDeque<Locatable<Token>>,
    ) -> Vec<Result<Token, CompileError>> {
        use std::mem;

        //let incoming = incoming.peekable();
        /*
        let mut no_replacement = VecDeque::new();
        // TODO: is this right? we need to be sure not to return this if `name` is replaced.
        no_replacement.push_back(Ok(Token::Id(name)));

        // cyclic define, e.g. `#define f(a) f(a + 1)`
        if self.ids_seen.contains(&name) {
            return no_replacement;
        }
        self.ids_seen.insert(name);
        */

        /*
        // check if this should be a function at all
        let (params, body) = match self.definitions.get(&name) {
            Some(Definition::Function { params, body }) => (params, body),
            _ => return no_replacement,
        };
        */
        let errors = Vec::new();

        //loop {
        match incoming.front() {
            // handle `f @ ( 1 )`, with arbitrarly many token errors
            /*
            Some(Err(err)) => {
                // TODO: need to figure out what should happen if an error token happens during replacement
                errors.push(Err(self.inner.next().unwrap().unwrap_err()));
            }
            */
            // f (
            Some(Locatable {
                data: Token::LeftParen,
                ..
            }) => {}
            // `f ;` or `f <EOF>`
            Some(_) | None => return errors,
        }
        //}

        // now, expand all arguments
        let mut args = Vec::new();
        let mut current_arg = Vec::new();
        let mut nested_parens = 1;

        loop {
            let next = match incoming.pop_front() {
                // f ( <EOF>
                // TODO: this should give an error
                None => return errors,
                // f ( @
                /*
                Some(Err(err)) => {
                    errors.push(Err(err));
                    continue;
                }
                */
                // f ( +
                Some(token) => token,
            };
            match next.data {
                // f ( a,
                // NOTE: `f(,)` is _legal_ and means to replace f with two arguments, each an empty token lists
                // on the bright side, we don't have to check if `current_arg` is empty or not
                Token::Comma if nested_parens == 1 => {
                    args.push(mem::take(&mut current_arg));
                    continue;
                }
                // f ( (a + 1)
                Token::RightParen => {
                    nested_parens -= 1;
                    // f ( )
                    if nested_parens == 0 {
                        args.push(mem::take(&mut current_arg));
                        break;
                    }
                }
                // f ( (
                Token::LeftParen => {
                    nested_parens += 1;
                }
                // f( + )
                _ => {}
            }
            // TODO: keep the location
            current_arg.push(next.data);
        }

        let mut replacements = Vec::new();
        if args.len() != params.len() {
            // booo, this is the _only_ error in the whole replacer
            return vec![Err(
                location.with(CppError::TooFewArguments(args.len(), params.len()).into())
            )];
        }
        for token in body {
            if let Token::Id(id) = *token {
                // #define f(a) { a + 1 } \n f(b) => b + 1
                if let Some(index) = params.iter().position(|&param| param == id) {
                    let replacement = args[index].clone();
                    replacements.extend(replacement);
                } else {
                    let token = Token::Id(id);
                    replacements.push(token);
                }
            } else {
                replacements.push(token.clone());
            }
        }
        // TODO: this collect is useless
        replacements.into_iter().map(Ok).collect()
        // NOTE: no errors could have occurred while parsing this function body
        // since they would have returned before getting here.
        //let first = self.pending.pop_front()?;
        //self.handle_token(first.data, first.location)
    }
}
