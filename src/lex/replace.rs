//! Macro replacement
//!
//! This module does no parsing and accepts only tokens.

use super::{cpp::CppResult, files::FileProcessor};
use crate::{
    error::CppError, CompileError, CompileResult, InternedStr, Locatable, Location, Token,
};
use std::collections::{HashMap, HashSet, VecDeque};

pub type Definitions = HashMap<InternedStr, Definition>;

pub trait Peekable: Iterator {
    fn peek(&mut self) -> Option<&Self::Item>;
}

impl Peekable for FileProcessor {
    fn peek(&mut self) -> Option<&Self::Item> {
        self.peek()
    }
}

impl<T: Iterator> Peekable for std::iter::Peekable<T> {
    fn peek(&mut self) -> Option<&Self::Item> {
        self.peek()
    }
}

impl<T> Peekable for std::iter::Empty<T> {
    fn peek(&mut self) -> Option<&Self::Item> {
        None
    }
}

impl<I: Peekable + ?Sized> Peekable for &mut I {
    fn peek(&mut self) -> Option<&Self::Item> {
        (**self).peek()
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
///
/// WARNING: if you call `replace()` the wrong way, you can cause an infinite loop.
/// Take for example this code (from [#298](https://github.com/jyn514/rcc/issues/298)):
/// ```c
/// #define sa_handler   __sa_handler.sa_handler
/// sa_handler
/// ```
/// If you implement a naive iterator on top of `MacroReplacer`,
/// you'll have a list of pending tokens (since a single underlying token can expand to many tokens).
/// If you then feed those tokens back to `replace` in a loop, they will generate infinitely many tokens:
/// `replace(sa_handler) -> yield __sa_handler; yield .; replace(sa_handler) -> ...`
/// The solution is to keep track of which tokens have already been replaced and not replace them a second time.
///
/// In most cases the above will not be relevant since you will only call `replace()` once,
/// or only call it on tokens which have not yet been replaced.
#[must_use = "does not change internal state"]
pub fn replace(
    definitions: &Definitions,
    token: Token,
    mut inner: impl Iterator<Item = CppResult<Token>> + Peekable,
    location: Location,
) -> Vec<CompileResult<Locatable<Token>>> {
    // The ids seen while replacing the current token.
    //
    // This allows cycle detection. It should be reset after every replacement list
    // - _not_ after every token, since otherwise that won't catch some mutual recursion
    // See https://github.com/jyn514/rcc/issues/427 for examples.
    let mut ids_seen = HashSet::new();
    let mut replacements = Vec::new();
    let mut pending = VecDeque::new();
    pending.push_back(Ok(location.with(token)));

    // outer loop: replace all tokens in the replacement list
    while let Some(token) = pending.pop_front() {
        // first step: perform (recursive) substitution on the ID
        if let Ok(Locatable {
            data: Token::Id(id),
            ..
        }) = token
        {
            if !ids_seen.contains(&id) {
                match definitions.get(&id) {
                    Some(Definition::Object(replacement_list)) => {
                        ids_seen.insert(id);
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
                        new_pending.extend(
                            replacement_list
                                .iter()
                                .cloned()
                                .map(|t| Ok(location.with(t))),
                        );
                        new_pending.append(&mut pending);
                        pending = new_pending;
                        continue;
                    }
                    // TODO: so many allocations :(
                    Some(Definition::Function { .. }) => {
                        ids_seen.insert(id);
                        let func_replacements =
                            replace_function(definitions, id, location, &mut pending, &mut inner);
                        let mut func_replacements: VecDeque<_> =
                            func_replacements.into_iter().collect();
                        func_replacements.append(&mut pending);
                        pending = func_replacements;
                        continue;
                    }
                    None => {}
                }
            }
        }
        replacements.push(token);
    }

    replacements
}

// TODO: this should probably return Result<VecDeque, CompileError> instead
#[must_use = "does not change internal state"]
fn replace_function(
    definitions: &Definitions,
    id: InternedStr,
    location: Location,
    incoming: &mut VecDeque<CompileResult<Locatable<Token>>>,
    mut inner: impl Iterator<Item = CppResult<Token>> + Peekable,
) -> Vec<Result<Locatable<Token>, CompileError>> {
    use std::mem;

    let mut errors = Vec::new();

    loop {
        match incoming.front().or_else(|| inner.peek()) {
            // handle `f @ ( 1 )`, with arbitrarly many token errors
            Some(Err(_)) => {
                let next = incoming.pop_front().or_else(|| inner.next());
                // TODO: need to figure out what should happen if an error token happens during replacement
                errors.push(Err(next.unwrap().unwrap_err()));
            }
            // f (
            Some(Ok(Locatable {
                data: Token::LeftParen,
                ..
            })) => {
                // pop off the `(` so it isn't counted as part of the first argument
                if incoming.pop_front().is_none() {
                    inner.next();
                }
                break;
            }
            // `f ;` or `f <EOF>`
            Some(_) | None => return errors,
        }
    }

    // now, expand all arguments
    let mut args = Vec::new();
    let mut current_arg = Vec::new();
    let mut nested_parens = 1;

    loop {
        let next = match incoming.pop_front().or_else(|| inner.next()) {
            // f ( <EOF>
            // TODO: this should give an error
            None => return errors,
            // f ( @
            Some(Err(err)) => {
                errors.push(Err(err));
                continue;
            }
            // f ( +
            Some(Ok(token)) => token,
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

    let (params, body) = match definitions.get(&id) {
        Some(Definition::Function { params, body }) => (params, body),
        // TODO: it would be nice to pass in `params` and `body` directly, but that runs into borrow errors
        _ => unreachable!("checked above"),
    };

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
    errors
        .into_iter()
        .chain(replacements.into_iter().map(|t| Ok(location.with(t))))
        .collect()
}
