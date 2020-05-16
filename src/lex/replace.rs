//! Macro replacement
//!
//! This module does no parsing and accepts only tokens.

use crate::{error::CppError, InternedStr, Token};
use std::collections::{HashMap, HashSet, VecDeque};

#[derive(Default)]
pub struct MacroReplacer {
    /// The ids seen while replacing the current token.
    ///
    /// This allows cycle detection. It should be reset after every replacement list
    /// - _not_ after every token, since otherwise that won't catch some mutual recursion
    /// See https://github.com/jyn514/rcc/issues/427 for examples.
    ids_seen: HashSet<InternedStr>,
    /// Note that this is a simple HashMap and not a Scope, because
    /// the preprocessor has no concept of scope other than `undef`
    pub definitions: HashMap<InternedStr, Definition>,
    /// The tokens that have been `#define`d and are currently being substituted
    pending: VecDeque<PendingToken>,
}

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
}

impl From<Token> for PendingToken {
    fn from(token: Token) -> Self {
        PendingToken::Replacement(token)
    }
}

#[derive(Debug)]
pub enum Definition {
    Object(Vec<Token>),
    Function {
        params: Vec<InternedStr>,
        body: Vec<Token>,
    },
}

impl MacroReplacer {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn with_definitions(definitions: HashMap<InternedStr, Definition>) -> Self {
        Self {
            definitions,
            ..Self::default()
        }
    }

    /// This function must be called after a single replacement list has finished being processed.
    pub(super) fn finished_replacement(&mut self) {
        self.ids_seen.clear();
    }

    /// Possibly recursively replace tokens. This also handles turning identifiers into keywords.
    ///
    /// If `token` was defined to an empty token list, this will return `None`.
    fn handle_token(&mut self, token: PendingToken) -> Option<Token> {
        let (token, needs_replacement) = match token {
            PendingToken::Replacement(tok) => (tok, true),
            PendingToken::Cyclic(tok) => (tok, false),
        };
        if let Token::Id(id) = token {
            if needs_replacement {
                return self.replace_id(id);
            }
        }
        Some(token)
    }

    /// Recursively replace the current identifier with its definitions.
    ///
    /// This does cycle detection by replacing the repeating identifier at least once;
    /// see the `recursive_macros` test for more details.
    // TODO: this needs to have an idea of 'pending chars', not just pending tokens
    pub fn replace_id(&mut self, mut name: InternedStr) -> Option<Token> {
        // first step: perform substitution on the ID
        while let Some(Definition::Object(def)) = self.definitions.get(&name) {
            self.ids_seen.insert(name);
            if def.is_empty() {
                return None;
            }
            let first = &def[0];

            if def.len() > 1 {
                // prepend the new tokens to the pending tokens
                // They need to go before, not after. For instance:
                // ```c
                // #define a b c d
                // #define b 1 + 2
                // a
                // ```
                // should replace to `1 + 2 c d`, not `c d 1 + 2`
                let mut new_pending = VecDeque::new();
                new_pending.extend(def[1..].iter().map(|token| {
                    let func = if let Token::Id(id) = token {
                        if self.ids_seen.contains(id) {
                            PendingToken::Cyclic
                        } else {
                            PendingToken::Replacement
                        }
                    } else {
                        PendingToken::Replacement
                        // we need a `clone()` because `self.definitions` needs to keep its copy of the definition
                    };
                    func(token.clone())
                }));
                new_pending.append(&mut self.pending);
                self.pending = new_pending;
            }

            // #define a b
            if let Token::Id(new_name) = first {
                name = *new_name;
                // recursive definition, stop now and return the current name.
                if self.ids_seen.contains(&name) {
                    break;
                }
            // #define a 1
            } else {
                return Some(first.clone());
            }
        }
        Some(Token::Id(name))
        // second step: perform function macro replacement
        //self.replace_function(name, start)
    }

    pub fn replace_function(
        &mut self,
        name: InternedStr,
        arguments: Vec<Vec<PendingToken>>,
    ) -> Result<Vec<PendingToken>, CppError> {
        let args = arguments;
        let no_replacement = |args: Vec<Vec<PendingToken>>| {
            let mut args = args.into_iter();
            let mut tokens = vec![Token::Id(name).into()];
            tokens.push(Token::LeftParen.into());
            if let Some(mut first) = args.next() {
                tokens.append(&mut first);
            }
            for mut arg in args {
                tokens.push(Token::Comma.into());
                tokens.append(&mut arg)
            }
            tokens.push(Token::RightParen.into());
            Ok(tokens)
        };
        // check if this should be a function at all
        if let Some(Definition::Function { .. }) = self.definitions.get(&name) {
        } else {
            return no_replacement(args);
        };
        // cyclic define, e.g. `#define f(a) f(a + 1)`
        if self.ids_seen.contains(&name) {
            return no_replacement(args);
        }

        self.ids_seen.insert(name);
        //let mut args = Vec::new();
        //let mut current_arg = Vec::new();
        //let body = unimplemented!();
        //let mut nested_parens = 1;
        // now, expand all arguments
        /*
        loop {
            let next = match arguments.next() {
                None => return body,
                Some(token) => token,
            };
            match next {
                Token::Comma if nested_parens == 1 => {
                    args.push(mem::take(&mut current_arg));
                    continue;
                }
                Token::RightParen => {
                    nested_parens -= 1;
                    if nested_parens == 0 {
                        args.push(mem::take(&mut current_arg));
                        break;
                    }
                }
                Token::LeftParen => {
                    nested_parens += 1;
                }
                _ => {}
            }
            current_arg.push(next);
        }
        */
        let (params, body) = match self.definitions.get(&name) {
            Some(Definition::Function { params, body }) => (params, body),
            _ => unreachable!("already checked this above"),
        };
        if args.len() != params.len() {
            // booo, this is the _only_ error in the whole replacer
            return Err(CppError::TooFewArguments(args.len(), params.len()));
        }
        for token in body {
            if let Token::Id(id) = *token {
                // #define f(a) { a + 1 } \n f(b) => b + 1
                if let Some(index) = params.iter().position(|&param| param == id) {
                    let replacement = args[index].clone();
                    self.pending.extend(replacement);
                } else {
                    let token = PendingToken::Replacement(Token::Id(id));
                    self.pending.push_back(token);
                }
            } else {
                self.pending
                    .push_back(PendingToken::Replacement(token.clone()));
            }
        }
        // TODO: this collect is bad
        Ok(std::mem::take(&mut self.pending).into_iter().collect())
        // NOTE: no errors could have occurred while parsing this function body
        // since they would have returned before getting here.
        //let first = self.pending.pop_front()?;
        //self.handle_token(first.data, first.location)
    }

    /*
    /// Given a token which needs replacement, return all tokens in the replacement list.
    ///
    /// Note that identifiers may be defined to be empty, so the list may not have any tokens.
    pub fn replace_all(&mut self, mut pending: Locatable<PendingToken>) -> Vec<Locatable<Token>> {
        let mut replacement_list = Vec::new();
        let pending = vec_deque![pending];
        while let Some(current) = pending.pop_front() {
            let (first, rest) = match self.replace(current) {
                Some(x) => x,
                None => continue,
            };
            replacement_list.push(first);
            pending.extend(rest);
        }
        replacement_list
        /*
        let (tok, needs_replacement) = match pending.data {
            PendingToken::Replacement(tok) => (tok, true),
            PendingToken::Cyclic(tok) => (tok, false),
        };
        if let Token::Id(id) = tok {
            if needs_replacement {
                return self.replace_id(id, pending.location);
            }
        }
        vec![pending]
        */
    }

    /// Replace a token.
    ///
    /// Note that a token may have many replacement tokens.
    /// This fully replaces the 'first' token and returns all remaining tokens without replacing them.
    /// 'first' is in quotes because replacements are recursive. Take the following example:
    /// ```c
    /// #define a b
    /// #define x y
    /// #define c a + x
    /// ```
    /// Calling `replace(c)` will return `[b, +, x]` _without_ replacing `x`.
    pub fn replace(&mut self, mut token: Locatable<PendingToken>) -> Option<(Locatable<Token>, VecDeque<Locatable<PendingToken>>)> {
        let mut replacement_list = VecDeque::new();
        loop {
            let (inner, needs_replacement) = match token.data {
                PendingToken::Replacement(tok) => (tok, true),
                PendingToken::Cyclic(tok) => (tok, false),
            };
            if let Token::Id(id) = inner {
                if needs_replacement {
                    let current_tokens = self.replace_id(id, token.location);
                    let first = current_tokens.pop_front();
                    // TODO: right now, `extend` is exactly as efficient as append,
                    // but in the future `append` might require fewer copies, so we could consider using a VecDeque
                    current_tokens.extend(replacement_list);
                    replacement_list = current_tokens;
                    token = first.or_else(|| replacement_list.pop_front())?;
                    continue;
                    //return self.replace_id(id, pending.location);
                }
            }
            return Some((Locatable::new(inner, token.location), replacement_list));
        }
    }

    /// Recursively replace the current identifier with its definitions.
    ///
    /// This does cycle detection by replacing the repeating identifier at least once;
    /// see the `recursive_macros` test for more details.
    // TODO: this needs to have an idea of 'pending chars', not just pending tokens
    fn replace_id(
        &mut self,
        mut name: InternedStr,
        location: Location,
    ) -> VecDeque<Locatable<PendingToken>> {
        let mut replacement_tokens = VecDeque::new();
        let start = self.offset();
        // first step: perform substitution on the ID until there is nothing left to replace
        while let Some(Definition::Object(def)) = self.definitions.get(&name) {
            self.ids_seen.insert(name);
            // #define a
            if def.is_empty() {
                return replacement_tokens;
            }
            let first = &def[0];

            // #define a 1 + 2
            if def.len() > 1 {
                // prepend the new tokens to the pending tokens
                // for instance, if we have
                // ```c
                // #define a b c d
                // #define b 1 + 2
                // a
                // ```
                // we should replace a with `1 + 2 c d`, not with `c d 1 + 2`
                replacement_tokens.extend(def[1..].iter().map(|token| {
                    let pending_tok = if let Token::Id(id) = token {
                        // `#define a a` (with arbitrarily many levels of recursion in between)
                        if self.ids_seen.contains(id) {
                            PendingToken::Cyclic
                        } else {
                            // #define a b
                            PendingToken::Replacement
                        }
                    // #define a +
                    } else {
                        PendingToken::Replacement
                        // we need a `clone()` because `self.definitions` needs to keep its copy of the definition
                    }(token.clone());
                    Locatable {
                        data: pending_tok,
                        location,
                    }
                }));
            }

            if let Token::Id(new_name) = first {
                name = *new_name;
                // recursive definition, stop now and return the current name.
                if self.ids_seen.contains(&name) {
                    break;
                }
            // #define ADD +
            } else {
                // This is what makes me think PendingToken isn't necessary
                replacement_tokens.push_front(Locatable::new(PendingToken::Replacement(first.clone()), self.span(start)));
                return replacement_tokens;
            }
        }
        // second step: perform function macro replacement
        self.replace_function(name, start)
    }
    fn replace_function(&mut self, name: InternedStr, start: u32) -> VecDeque<Locatable<PendingToken>> {
        use std::mem;
        let no_replacement =
            |this: &mut Self| vec_deque![Locatable::new(PendingToken::Cyclic(Token::Id(name)), this.span(start))];
        // check if this should be a function at all
        if let Some(Definition::Function { .. }) = self.definitions.get(&name) {
        } else {
            return no_replacement(self);
        };
        // cyclic define, e.g. `#define f(a) f(a + 1)`
        if self.ids_seen.contains(&name) {
            return no_replacement(self);
        }
        loop {
            match self.match_next(Token::LeftParen) {
                Err(err) => self.error_handler.push_back(err),
                Ok(None) => return no_replacement(self),
                Ok(Some(_)) => break,
            }
        }

        self.ids_seen.insert(name);
        let location = self.span(start);
        let mut args = Vec::new();
        let mut current_arg = Vec::new();
        let mut nested_parens = 1;
        // now, expand all arguments
        loop {
            let next = match self.next_replacement_token() {
                None => return vec_deque![],
                Some(Err(err)) => return Some(Err(err)),
                Some(Ok(token)) => token,
            };
            match next.data.token() {
                Token::Comma if nested_parens == 1 => {
                    args.push(mem::take(&mut current_arg));
                    continue;
                }
                Token::RightParen => {
                    nested_parens -= 1;
                    if nested_parens == 0 {
                        args.push(mem::take(&mut current_arg));
                        break;
                    }
                }
                Token::LeftParen => {
                    nested_parens += 1;
                }
                _ => {}
            }
            current_arg.push(next);
        }
        let (params, body) = match self.definitions.get(&name) {
            Some(Definition::Function { params, body }) => (params, body),
            _ => unreachable!("already checked this above"),
        };
        if args.len() != params.len() {
            return Some(Err(CompileError::new(
                CppError::TooFewArguments(args.len(), params.len()).into(),
                self.span(start),
            )));
        }
        for token in body {
            if let Token::Id(id) = *token {
                // #define f(a) { a + 1 } \n f(b) => b + 1
                if let Some(index) = params.iter().position(|&param| param == id) {
                    let replacement = args[index].clone();
                    self.pending.extend(replacement);
                } else {
                    let token = PendingToken::Replacement(Token::Id(id));
                    self.pending.push_back(location.with(token));
                }
            } else {
                self.pending
                    .push_back(location.with(PendingToken::Replacement(token.clone())));
            }
        }
        // NOTE: no errors could have occurred while parsing this function body
        // since they would have returned before getting here.
        let first = self.pending.pop_front()?;
        self.replace(first)
    }
    */
}
