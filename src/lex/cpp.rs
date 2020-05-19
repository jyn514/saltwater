use lazy_static::lazy_static;

use std::borrow::Cow;
use std::collections::{HashMap, VecDeque};
use std::convert::TryFrom;
use std::path::{Path, PathBuf};
use std::rc::Rc;

use super::replace::{Definition, MacroReplacer};
use super::{Lexer, Token};
use crate::arch::TARGET;
use crate::data::error::CppError;
use crate::data::lex::{Keyword, Literal};
use crate::data::*;
use crate::get_str;
use crate::Files;

/// An easier interface for constructing a preprocessor.
///
/// Here is the example for `PreProcessor::new()` using the builder:
/// ```
/// use rcc::PreProcessorBuilder;
///
/// let cpp = PreProcessorBuilder::new("int main(void) { char *hello = \"hi\"; }\n").filename("example.c").build();
/// for token in cpp {
///     assert!(token.is_ok());
/// }
/// ```
pub struct PreProcessorBuilder<'a> {
    /// The buffer for the starting file
    buf: Rc<str>,
    /// The name of the file
    filename: PathBuf,
    /// Whether to print each token before replacement
    debug: bool,
    /// The paths to search for `#include`d files
    search_path: Vec<Cow<'a, Path>>,
    /// The user-defined macros that should be defined at startup
    definitions: HashMap<InternedStr, Definition>,
}

impl<'a> PreProcessorBuilder<'a> {
    pub fn new<S: Into<Rc<str>>>(buf: S) -> PreProcessorBuilder<'a> {
        PreProcessorBuilder {
            debug: false,
            filename: PathBuf::default(),
            buf: buf.into(),
            search_path: Vec::new(),
            definitions: HashMap::new(),
        }
    }
    pub fn filename<P: Into<PathBuf>>(mut self, name: P) -> Self {
        self.filename = name.into();
        self
    }
    pub fn debug(mut self, yes: bool) -> Self {
        self.debug = yes;
        self
    }
    pub fn search_path<C: Into<Cow<'a, Path>>>(mut self, path: C) -> Self {
        self.search_path.push(path.into());
        self
    }
    pub fn definition<D: Into<Definition>>(mut self, name: InternedStr, def: D) -> Self {
        self.definitions.insert(name, def.into());
        self
    }
    pub fn build(self) -> PreProcessor<'a> {
        PreProcessor::new(
            self.buf,
            self.filename,
            self.debug,
            self.search_path,
            self.definitions,
        )
    }
}

enum Unimplemented {}
impl Iterator for Unimplemented {
    type Item = CppResult<Token>;
    fn next(&mut self) -> Option<Self::Item> {
        None
    }
}

impl Default for Unimplemented {
    fn default() -> Self {
        unimplemented!()
    }
}

/// A preprocessor does textual substitution and deletion on a C source file.
///
/// The C preprocessor, or `cpp`, is tightly tied to C tokenization.
/// Rules for tokenizing identifiers, operators, and literals are all the same,
/// so you can't use it to preprocess e.g. Haskell, where `a'` is a valid identifier.
///
/// The preprocessor is further tied to the lexer because it is whitespace dependent:
/// `#define a() b` is _not_ the same as `#define a () b`.
/// The first is a function-like macro; the second is an object-like macro.
///
/// The preprocessor has no concept of scope: everything is either defined or not defined.
/// Variables can only be defined as strings, or more accurately, token sequences.
///
/// It is possible to tell the difference between an undefined variable
/// and a variable defined to be empty using `#ifdef var` and `#if var`.
///
/// Examples:
///
/// ```
/// use rcc::PreProcessor;
///
/// let cpp = PreProcessor::new("int main(void) { char *hello = \"hi\"; }\n", "example.c", false, vec![], Default::default());
/// for token in cpp {
///     assert!(token.is_ok());
/// }
/// ```
pub struct PreProcessor<'a> {
    /// The preprocessor collaborates extremely closely with the lexer,
    /// since it sometimes needs to know if a token is followed by whitespace.
    first_lexer: Lexer,
    /// Each lexer represents a separate source file that is currently being processed.
    includes: Vec<Lexer>,
    /// All known files, including files which have already been read.
    files: Files,
    error_handler: ErrorHandler,
    /// Keeps track of current `#if` directives
    nested_ifs: Vec<IfState>,
    /// The paths to search for `#include`d files
    search_path: Vec<Cow<'a, Path>>,
    /// The tokens that have been `#define`d and are currently being substituted
    pending: VecDeque<Locatable<Token>>,
    /// The macro-replacer
    replacer: MacroReplacer,
}

impl From<Token> for CppToken {
    fn from(t: Token) -> CppToken {
        CppToken::Token(t)
    }
}

impl From<Vec<Token>> for Definition {
    fn from(tokens: Vec<Token>) -> Definition {
        Definition::Object(tokens)
    }
}

impl TryFrom<&str> for Definition {
    type Error = error::LexError;
    fn try_from(value: &str) -> Result<Self, Self::Error> {
        let value = Rc::from(format!("{}\n", value));
        let mut files = codespan::Files::new();
        let dummy_id = files.add("<impl TryFrom<&str> for Definition>", Rc::clone(&value));
        let lexer = Lexer::new(dummy_id, value, false);
        lexer
            .map(|res| match res {
                Ok(loc) => Ok(loc.data),
                Err(err) => Err(err.data),
            })
            .collect::<Result<_, _>>()
            .map(Definition::Object)
    }
}

/// Keeps track of the state of a conditional inclusion directive.
///
/// `If` means we are currently processing an `#if`,
/// `Elif` means an `#elif`, and `Else` means an `#else`.
///
/// There are more states, but they are tracked internally to `consume_directive()`.
/// The state diagram looks like this (pipe to `xdot -` for visualization):
///
/// ```dot
/// strict digraph if_state {
///    IF [label="self.nested_ifs.push(If)"];
///    ELIF [label="self.nested_ifs.push(Elif)"];
///    ELSE [label="self.nested_ifs.push(Else)"];
///    END [label="self.nested_ifs.pop()"];
///
///    start -> IF [label="#if 1"]
///    IF -> END [label="#endif"]
///    IF -> consume_all [label="#elif ... / #else"]
///    consume_all -> END [label="#endif"]
///
///    start -> consume_if [label="#if 0"]
///    consume_if -> consume_if [label="#elif 0"]
///    consume_if -> ELIF [label="#elif 1"]
///    consume_if -> ELSE [label="#else"]
///    consume_if -> END  [label="#endif"]
///
///    ELIF -> consume_all [label="#elif ... / #else"]
///    ELIF -> END         [label="#endif"]
///
///    ELSE -> END [label="#endif"]
///  }
/// ```
#[derive(Debug)]
enum IfState {
    If,
    Elif,
    Else,
}

pub(super) type CppResult<T> = Result<Locatable<T>, CompileError>;

impl Iterator for PreProcessor<'_> {
    /// The preprocessor hides all internal complexity and returns only tokens.
    type Item = CppResult<Token>;
    fn next(&mut self) -> Option<Self::Item> {
        // We have two things we need to handle.
        // First, we could have gotten to the end of the file;
        // Second, the current token could be an identifier that was `#define`d to an empty token list.
        // This loop is for the second case, not the first.
        loop {
            let replacement = if let Some(err) = self.error_handler.pop_front() {
                return Some(Err(err));
            } else if let Some(token) = self.pending.pop_front() {
                self.handle_token(token.data, token.location)
            } else {
                //self.replacer.finished_replacement();
                // This function does not perform macro replacement,
                // so if it returns None we got to EOF.
                match self.next_cpp_token()? {
                    Err(err) => return Some(Err(err)),
                    Ok(loc) => match loc.data {
                        CppToken::Directive(directive) => {
                            let start = loc.location.span.start;
                            match self.directive(directive, start) {
                                Err(err) => return Some(Err(err)),
                                Ok(()) => continue,
                            }
                        }
                        CppToken::Token(token) => self.handle_token(token, loc.location),
                    },
                }
            };
            if let Some(token) = replacement {
                return Some(token);
            }
            // This token was an empty define, so continue looking for tokens
        }
    }
}

// idiom: to check if there has been a newline since the last token,
// use the following pattern:
// ```rust
// let line = self.lexer.line;
// ... do stuff that consumes tokens ...
// let seen_newline = line == self.lexer.line;
// ```
impl<'a> PreProcessor<'a> {
    /// Since there could potentially be multiple lexers (for multiple files),
    /// this is a convenience function that returns the lexer for the current file.
    fn lexer(&self) -> &Lexer {
        self.includes.last().unwrap_or(&self.first_lexer)
    }
    /// Same as `lexer()` but `&mut self -> &mut Lexer`.
    fn lexer_mut(&mut self) -> &mut Lexer {
        self.includes.last_mut().unwrap_or(&mut self.first_lexer)
    }
    /*
    /// Return the next token, taking into account replacements
    fn next_replacement_token(&mut self) -> Option<CppResult<Token>> {
        // TODO: need to call `replace()` at some point
        if let Some(replacement) = self.pending.pop_front() {
            return Some(Ok(replacement));
        }
        match self.lexer_mut().next()? {
            Err(err) => Some(Err(err.map(Into::into))),
            Ok(token) => Some(Ok(token)),
        }
    }
    /// If the next token is a `token`, consume it and return its location.
    /// Note: this takes into account token replacement.
    fn match_next(&mut self, token: Token) -> Result<Option<Location>, CompileError> {
        match self.next_replacement_token() {
            None => Ok(None),
            Some(Err(err)) => Err(err),
            Some(Ok(next)) => {
                if next.data == token {
                    Ok(Some(next.location))
                } else {
                    self.pending.push_front(next);
                    Ok(None)
                }
            }
        }
    }
    */
    /* Convenience functions */
    #[inline]
    fn line(&self) -> usize {
        self.lexer().line
    }
    #[inline]
    fn next_token(&mut self) -> Option<CppResult<Token>> {
        Some(self.lexer_mut().next()?.map_err(CompileError::from))
    }
    #[inline]
    fn span(&self, start: u32) -> Location {
        self.lexer().span(start)
    }
    #[inline]
    fn consume_whitespace(&mut self) {
        self.lexer_mut().consume_whitespace()
    }
    #[inline]
    fn seen_line_token(&self) -> bool {
        self.lexer().seen_line_token
    }
    #[inline]
    fn offset(&self) -> u32 {
        self.lexer().location.offset
    }
    /// Possibly recursively replace tokens. This also handles turning identifiers into keywords.
    ///
    /// If `token` was defined to an empty token list, this will return `None`.
    fn handle_token(&mut self, token: Token, location: Location) -> Option<CppResult<Token>> {
        //if let Token::Id(id) = token {
        let mut token = {
            let mut replacement_list = self.replacer.replace(token, location).into_iter();
            //.map(|res| res.map(|t| Locatable::new(t, location)));
            let first = replacement_list.next();
            for remaining in replacement_list {
                match remaining {
                    Err(err) => self.error_handler.push_back(err),
                    Ok(token) => self.pending.push_back(token),
                }
            }
            //self.pending.extend(replacement_list);
            first
            /*
            } else {
                Some(Ok(Locatable::new(token, location)))
                */
        };
        if let Some(Ok(Locatable {
            data: data @ Token::Id(_),
            ..
        })) = &mut token
        {
            if let Token::Id(name) = &data {
                if let Some(keyword) = KEYWORDS.get(get_str!(name)) {
                    *data = Token::Keyword(*keyword);
                }
            }
        }
        token
        /*
        } else {
            Some(Ok(Locatable::new(token, location)))
        }
        */
    }

    /*
    pub fn replace(&mut self, id: InternedStr, start: u32) -> Option<CppResult<Token>> {
        use std::mem;

        let id = match self.replacer.replace_id(id) {
            Some(Token::Id(id)) => id,
            Some(other) => return Some(Ok(Locatable::new(other, self.span(start)))),
            None => return None,
        };
        // NOTE: this does _not_ consume whitespace
        loop {
            match self.match_next(Token::LeftParen) {
                Err(err) => self.error_handler.push_back(err),
                Ok(None) => return Some(Ok(Locatable::new(Token::Id(id), self.span(start)))),
                Ok(Some(_)) => break,
            }
        }
        let location = self.span(start);
        let mut args = Vec::new();
        let mut current_arg = Vec::new();
        let mut nested_parens = 1;
        // now, expand all arguments
        loop {
            let next = match self.next_replacement_token() {
                None => return None,
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
            // TODO: keep the location
            current_arg.push(next.data);
        }
        let mut body = match self.replacer.replace_function(id, args) {
            Ok(body) => body.into_iter(),
            Err(err) => return Some(Err(Locatable::new(err.into(), self.span(start)))),
        };
        let first = body.next()?;
        // lol let's just give them all the same span
        let loc = self.span(start);
        self.pending.extend(body.map(|tok| loc.with(tok)));
        self.handle_token(first, loc)
    }
    */

    /// Create a new preprocessor for the file identified by `file`.
    ///
    /// Note that the preprocessor may add arbitrarily many `#include`d files to `files`,
    /// but will never delete a file.
    ///
    /// The `debug` parameter specifies whether to print out tokens before replacement.
    pub fn new<'search: 'a, I: IntoIterator<Item = Cow<'search, Path>>, S: Into<Rc<str>>>(
        chars: S,
        filename: impl Into<std::ffi::OsString>,
        debug: bool,
        user_search_path: I,
        user_definitions: HashMap<InternedStr, Definition>,
    ) -> Self {
        let system_path = format!(
            "{}-{}-{}",
            TARGET.architecture, TARGET.operating_system, TARGET.environment
        );
        let int = |i| Definition::Object(vec![Token::Literal(Literal::Int(i))]);

        #[allow(clippy::inconsistent_digit_grouping)]
        let mut definitions = map! {
            format!("__{}__", TARGET.architecture).into() => int(1),
            format!("__{}__", TARGET.operating_system).into() => int(1),
            "__STDC__".into() => int(1),
            "__STDC_HOSTED__".into() => int(1),
            "__STDC_VERSION__".into() => int(2011_12),
            "__STDC_NO_ATOMICS__".into() => int(1),
            "__STDC_NO_COMPLEX__".into() => int(1),
            "__STDC_NO_THREADS__".into() => int(1),
            "__STDC_NO_VLA__".into() => int(1),
        };
        definitions.extend(user_definitions);
        let mut search_path = vec![
            PathBuf::from(format!("/usr/local/include/{}", system_path)).into(),
            Path::new("/usr/local/include").into(),
            PathBuf::from(format!("/usr/include/{}", system_path)).into(),
            Path::new("/usr/include").into(),
        ];
        search_path.extend(user_search_path.into_iter());

        let mut files = Files::new();
        let chars = chars.into();
        let filename = filename.into();
        let source = crate::Source {
            code: Rc::clone(&chars),
            path: filename.clone().into(),
        };
        let file = files.add(filename, source);

        Self {
            first_lexer: Lexer::new(file, chars, debug),
            includes: Default::default(),
            error_handler: Default::default(),
            nested_ifs: Default::default(),
            pending: Default::default(),
            files,
            search_path,
            replacer: MacroReplacer::with_definitions(definitions),
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
        std::mem::take(&mut self.error_handler.warnings)
    }

    /// Return a `Location` representing the end of the first file.
    pub fn eof(&self) -> Location {
        let lex = &self.first_lexer;
        Location {
            span: (lex.chars.len() as u32..lex.chars.len() as u32).into(),
            file: lex.location.file,
        }
    }

    /// Return all files loaded by the preprocessor, consuming it in the process.
    ///
    /// Files can be loaded by C source using `#include` directives.
    pub fn into_files(self) -> Files {
        self.files
    }

    /* internal functions */
    /// Return all tokens from the current position until the end of the current line.
    ///
    /// Note that these are _tokens_ and not bytes, so if there are invalid tokens
    /// on the current line, this will return a lex error.
    fn tokens_until_newline(&mut self) -> Vec<CompileResult<Locatable<Token>>> {
        let mut tokens = Vec::new();
        let line = self.line();
        loop {
            self.consume_whitespace();
            if self.line() != line {
                // lines should end with a newline, but in case they don't, don't crash
                assert!(!self.lexer().seen_line_token || self.lexer_mut().peek().is_none(),
                    "expected `tokens_until_newline()` to reset `seen_line_token`, but `lexer.peek()` is {:?}",
                    self.lexer_mut().peek());
                break;
            }
            match self.next_token() {
                Some(token) => tokens.push(token),
                None => break,
            }
        }
        tokens
    }

    /// If at the start of the line and we see `#directive`, return that directive.
    /// Otherwise, if we see a token (or error), return that error.
    /// Otherwise, return `None`.
    fn next_cpp_token(&mut self) -> Option<CppResult<CppToken>> {
        let next_token = loop {
            // we have to duplicate a bit of code here to avoid borrow errors
            let lexer = self.includes.last_mut().unwrap_or(&mut self.first_lexer);
            match lexer.next() {
                Some(token) => break token,
                // finished this file, go on to the next one
                None => {
                    self.error_handler.append(&mut lexer.error_handler);
                    // this is the original source file
                    if self.includes.is_empty() {
                        return None;
                    } else {
                        self.includes.pop();
                    }
                }
            }
        };
        let is_hash = match next_token {
            Ok(Locatable {
                data: Token::Hash, ..
            }) => true,
            _ => false,
        };
        Some(if is_hash && !self.seen_line_token() {
            let line = self.line();
            match self.next_token()? {
                Ok(Locatable {
                    data: Token::Id(id),
                    location,
                }) if self.line() == line => {
                    if let Ok(directive) = DirectiveKind::try_from(get_str!(id)) {
                        Ok(Locatable::new(CppToken::Directive(directive), location))
                    } else {
                        Err(Locatable::new(CppError::InvalidDirective.into(), location))
                    }
                }
                Ok(other) => {
                    if self.line() == line {
                        Err(other.map(|tok| CppError::UnexpectedToken("directive", tok).into()))
                    } else {
                        Ok(other.into())
                    }
                }
                other => other.map(Locatable::from),
            }
        } else {
            next_token.map(Locatable::from).map_err(|err| err.into())
        })
    }
    // this function does _not_ perform macro substitution
    fn expect_id(&mut self) -> CppResult<InternedStr> {
        let location = self.span(self.offset());
        match self.next_token() {
            Some(Ok(Locatable {
                data: Token::Id(name),
                location,
            })) => Ok(Locatable::new(name, location)),
            Some(Err(err)) => Err(err),
            Some(Ok(other)) => {
                Err(other.map(|tok| CppError::UnexpectedToken("identifier", tok).into()))
            }
            None => Err(CompileError {
                data: CppError::EndOfFile("identifier").into(),
                location,
            }),
        }
    }
    // Handle a directive. This assumes we have consumed the directive (e.g. `#if`),
    // but not the rest of the tokens on the current line.
    fn directive(&mut self, kind: DirectiveKind, start: u32) -> Result<(), CompileError> {
        use crate::data::error::Warning as WarningDiagnostic;
        use DirectiveKind::*;
        match kind {
            If => {
                let condition = self.boolean_expr()?;
                self.if_directive(condition, start)
            }
            IfNDef => {
                let name = self.expect_id()?;
                self.if_directive(!self.replacer.definitions.contains_key(&name.data), start)
            }
            IfDef => {
                let name = self.expect_id()?;
                self.if_directive(self.replacer.definitions.contains_key(&name.data), start)
            }
            // No matter what happens here, we will not read the tokens from this `#elif`.
            // Either we have been reading an `#if` or an `#elif` or an `#else`;
            // in any case, this `#elif` will be ignored.
            Elif => match self.nested_ifs.last() {
                None => Err(CompileError::new(
                    CppError::UnexpectedElif { early: true }.into(),
                    self.span(start),
                )),
                // saw a previous #if or #elif, consume all following directives
                // `If` / `Elif` -> `consume_all`
                Some(IfState::If) | Some(IfState::Elif) => self.consume_directive(start, false),
                Some(IfState::Else) => Err(CompileError::new(
                    CppError::UnexpectedElif { early: false }.into(),
                    self.span(start),
                )),
            },
            Else => match self.nested_ifs.last() {
                None => Err(CompileError::new(
                    CppError::UnexpectedElse.into(),
                    self.span(start),
                )),
                // we already took the `#if` condition,
                // `#else` should just be ignored
                // `Else` -> `consume_all`
                Some(IfState::If) | Some(IfState::Elif) => self.consume_directive(start, false),
                // we saw an `#else` before, seeing it again is an error
                Some(IfState::Else) => Err(CompileError::new(
                    CppError::UnexpectedElse.into(),
                    self.span(start),
                )),
            },
            EndIf => {
                if self.nested_ifs.pop().is_none() {
                    Err(CompileError::new(
                        CppError::UnexpectedEndIf.into(),
                        self.span(start),
                    ))
                } else {
                    Ok(())
                }
            }
            Define => self.define(start),
            Undef => {
                let name = self.expect_id()?;
                self.replacer.definitions.remove(&name.data);
                Ok(())
            }
            Pragma => {
                self.error_handler
                    .warn(WarningDiagnostic::IgnoredPragma, self.span(start));
                drop(self.tokens_until_newline());
                Ok(())
            }
            // NOTE: #warning is a non-standard extension, but is implemented
            // by most major compilers including clang and gcc.
            Warning => {
                let tokens: Vec<_> = self
                    .tokens_until_newline()
                    .into_iter()
                    .map(|res| res.map(|l| l.data))
                    .collect::<Result<_, _>>()?;
                self.error_handler
                    .warn(WarningDiagnostic::User(tokens), self.span(start));
                Ok(())
            }
            Error => {
                let tokens: Vec<_> = self
                    .tokens_until_newline()
                    .into_iter()
                    .map(|res| res.map(|l| l.data))
                    .collect::<Result<_, _>>()?;
                self.error_handler
                    .error(CppError::User(tokens), self.span(start));
                Ok(())
            }
            Line => {
                self.error_handler.warn(
                    WarningDiagnostic::Generic("#line is not yet implemented".into()),
                    self.span(start),
                );
                drop(self.tokens_until_newline());
                Ok(())
            }
            Include => self.include(start),
        }
    }
    // convienience function around cpp_expr
    fn boolean_expr(&mut self) -> Result<bool, CompileError> {
        // TODO: is this unwrap safe? there should only be scalar types in a cpp directive...
        match self
            .cpp_expr()?
            .truthy(&mut self.error_handler)
            .constexpr()?
            .data
        {
            (Literal::Int(i), Type::Bool) => Ok(i != 0),
            _ => unreachable!("bug in const_fold or parser: cpp cond should be boolean"),
        }
    }
    // `#if defined(a)` or `#if defined a`
    // http://port70.net/~nsz/c/c11/n1570.html#6.10.1p1
    fn defined(
        lex_tokens: &mut impl Iterator<Item = Result<Locatable<Token>, CompileError>>,
        cpp_tokens: &mut Vec<Result<Locatable<Token>, CompileError>>,
        location: Location,
    ) -> Result<InternedStr, CompileError> {
        enum State {
            Start,
            SawParen,
            SawId(InternedStr),
        };
        use State::*;
        let mut state = Start;
        loop {
            return match lex_tokens.next() {
                None => Err(CompileError::new(
                    CppError::EndOfFile("defined(identifier)").into(),
                    location,
                )),
                Some(Err(err)) => {
                    cpp_tokens.push(Err(err));
                    continue;
                }
                Some(Ok(Locatable {
                    data: Token::Id(def),
                    location,
                })) => match state {
                    Start => Ok(def),
                    SawParen => {
                        state = SawId(def);
                        continue;
                    }
                    SawId(_) => Err(CompileError::new(
                        CppError::UnexpectedToken("right paren", Token::Id(def)).into(),
                        location,
                    )),
                },
                Some(Ok(Locatable {
                    data: Token::LeftParen,
                    location,
                })) => match state {
                    Start => {
                        state = SawParen;
                        continue;
                    }
                    _ => Err(CompileError::new(
                        CppError::UnexpectedToken("identifier or right paren", Token::LeftParen)
                            .into(),
                        location,
                    )),
                },
                Some(Ok(Locatable {
                    data: Token::RightParen,
                    location,
                })) => match state {
                    Start => Err(CompileError::new(
                        CppError::UnexpectedToken("identifier or left paren", Token::RightParen)
                            .into(),
                        location,
                    )),
                    SawParen => Err(CompileError::new(
                        CppError::UnexpectedToken("identifier", Token::RightParen).into(),
                        location,
                    )),
                    SawId(def) => Ok(def),
                },
                Some(Ok(other)) => Err(CompileError::new(
                    CppError::UnexpectedToken("identifier", other.data).into(),
                    other.location,
                )),
            };
        }
    }
    /// A C expression on a single line. Used for `#if` directives.
    ///
    /// Note that identifiers are replaced with a constant 0,
    /// as per [6.10.1](http://port70.net/~nsz/c/c11/n1570.html#6.10.1p4).
    fn cpp_expr(&mut self) -> Result<hir::Expr, CompileError> {
        let start = self.offset();
        let defined = "defined".into();

        let lex_tokens = self.tokens_until_newline();
        let mut cpp_tokens = Vec::with_capacity(lex_tokens.len());
        //assert!(self.replacer.pending.is_empty());
        let mut lex_tokens = lex_tokens
            .into_iter()
            .map(|res| res.map(|t| self.replacer.replace(t.data, t.location)))
            .flatten()
            .flatten()
            .collect::<Vec<_>>()
            .into_iter();
        while let Some(token) = lex_tokens.next() {
            let token = match token {
                // #if defined(a)
                Ok(Locatable {
                    data: Token::Id(name),
                    location,
                }) if name == defined => {
                    let def = Self::defined(&mut lex_tokens, &mut cpp_tokens, location)?;
                    let literal = if self.replacer.definitions.contains_key(&def) {
                        Literal::Int(1)
                    } else {
                        Literal::Int(0)
                    };
                    Ok(location.with(Token::Literal(literal)))
                }
                // #if a
                Ok(Locatable {
                    data: Token::Id(_),
                    location,
                }) => {
                    let token = Token::Literal(Literal::Int(0));
                    Ok(Locatable::new(token, location))
                }
                // #if 1
                _ => token,
            };
            cpp_tokens.push(token);
        }
        if cpp_tokens.is_empty() {
            return Err(CompileError::new(
                CppError::EmptyExpression.into(),
                self.span(start),
            ));
        }
        // TODO: remove(0) is bad and I should feel bad
        // TODO: this only returns the first error because anything else requires a refactor
        let first = cpp_tokens.remove(0)?;
        use crate::{analyze::PureAnalyzer, Parser};
        let mut parser = Parser::new(first, cpp_tokens.into_iter(), false);
        let expr = parser.expr()?;
        // TODO: catch expressions that aren't allowed
        // (see https://github.com/jyn514/rcc/issues/5#issuecomment-575339427)
        // TODO: can semantic errors happen here? should we check?
        Ok(PureAnalyzer::new().expr(expr))
    }
    /// We saw an `#if`, `#ifdef`, or `#ifndef` token at the start of the line
    /// and want to either take the branch or ignore the tokens within the directive.
    fn if_directive(&mut self, condition: bool, start: u32) -> Result<(), CompileError> {
        if condition {
            // start -> IF
            self.nested_ifs.push(IfState::If);
            Ok(())
        } else {
            // `start` -> `consume_if`
            self.consume_directive(start, true)
        }
    }
    /// Keep consuming tokens until `#endif`.
    /// This has to take into account nesting of #if directives.
    ///
    /// `consume_if` indicates whether this is the `consume_if` or `consume_all` state.
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
    fn consume_directive(&mut self, start: u32, consume_if: bool) -> Result<(), CompileError> {
        let mut depth = 1;
        while depth > 0 {
            let directive = match self.next_cpp_token() {
                Some(Ok(Locatable {
                    data: CppToken::Directive(d),
                    ..
                })) => d,
                Some(_) => continue,
                None => {
                    return Err(Locatable::new(CppError::UnterminatedIf, self.span(start)).into())
                }
            };
            if directive == DirectiveKind::If
                || directive == DirectiveKind::IfDef
                || directive == DirectiveKind::IfNDef
            {
                depth += 1;
            } else if directive == DirectiveKind::EndIf {
                depth -= 1;
            // Note the only directives left are #elif and #else.
            // If depth >= 2, they are just ignored.
            } else if depth == 1 {
                // `consume_if` from the state diagram
                if consume_if {
                    if directive == DirectiveKind::Elif {
                        let condition = self.boolean_expr()?;
                        if !condition {
                            // stay in the same `consume_if` state
                            continue;
                        } else {
                            // go to `Elif` state
                            self.nested_ifs.push(IfState::Elif);
                            return Ok(());
                        }
                    // go to `Else` state
                    } else if directive == DirectiveKind::Else {
                        self.nested_ifs.push(IfState::Else);
                        return Ok(());
                    }
                    // otherwise, keep consuming tokens
                }
                // `consume_all` from the state diagram: all directives ignored
            }
        }
        Ok(())
    }
    // Consumes tokens like this:
    // before:
    // #define f(a, b, c) a + b + c
    //           ^
    // after:
    // #define f(a, b, c) a + b + c
    //                   ^
    fn fn_args(&mut self, start: u32) -> Result<Vec<InternedStr>, Locatable<Error>> {
        let mut arguments = Vec::new();
        loop {
            match self.next_token() {
                None => {
                    return Err(CompileError::new(
                        CppError::EndOfFile("identifier or ')'").into(),
                        // TODO: I think this will be wrong if the file
                        // the macro started in was not the same as the one it ended in
                        self.lexer().span(start),
                    ));
                }
                Some(Err(err)) => {
                    self.error_handler.push_back(err);
                    continue;
                }
                Some(Ok(Locatable {
                    data: Token::Ellipsis,
                    ..
                })) => self.error_handler.warn(
                    crate::data::error::Warning::IgnoredVariadic,
                    self.lexer().span(start),
                ),
                Some(Ok(Locatable {
                    data: Token::Id(id),
                    ..
                })) => arguments.push(id),
                Some(Ok(Locatable {
                    data: other,
                    location,
                })) => self.error_handler.error(
                    CppError::UnexpectedToken("identifier or ')'", other),
                    location,
                ),
            }
            // either `,` or `)`
            if self.lexer_mut().match_next(b')') {
                return Ok(arguments);
            }
            if self.lexer_mut().match_next(b',') {
                continue;
            }
            // some other token
            match self.next_token() {
                None => {
                    return Err(CompileError::new(
                        CppError::EndOfFile("identifier or ')'").into(),
                        self.lexer().span(start),
                    ))
                }
                Some(Err(err)) => return Err(err),
                Some(Ok(other)) => self.error_handler.error(
                    CppError::UnexpectedToken("',' or ')'", other.data),
                    other.location,
                ),
            }
        }
    }
    // http://port70.net/~nsz/c/c11/n1570.html#6.10.3
    // `#define a b` - object macro
    // `#define f(a) a` - function macro
    // `#define f (a) - object macro
    fn define(&mut self, start: u32) -> Result<(), Locatable<Error>> {
        let body = |this: &mut PreProcessor| {
            this.tokens_until_newline()
                .into_iter()
                .map(|res| res.map(|loc| loc.data))
                .collect::<Result<Vec<_>, Locatable<Error>>>()
        };

        let line = self.line();
        self.consume_whitespace();
        if self.line() != line {
            return Err(self.span(start).error(CppError::EmptyDefine));
        }
        let id = self.expect_id()?;
        // NOTE: does _not_ discard whitespace
        if self.lexer_mut().match_next(b'(') {
            // function macro
            // first, parse the arguments:
            // # define identifier lparen identifier-listopt ) replacement-list new-line
            // # define identifier lparen ... ) replacement-list new-line
            // # define identifier lparen identifier-list , ... ) replacement-list new-line
            self.lexer_mut().consume_whitespace();
            let params = if !self.lexer_mut().match_next(b')') {
                self.fn_args(start)?
            } else {
                Vec::new()
            };
            let body = body(self)?;
            self.replacer
                .definitions
                .insert(id.data, Definition::Function { params, body });
            Ok(())
        } else {
            // object macro
            let tokens = body(self)?;
            self.replacer
                .definitions
                .insert(id.data, Definition::Object(tokens));
            Ok(())
        }
    }
    // http://port70.net/~nsz/c/c11/n1570.html#6.10.2
    // `#include <file>` - system include
    // `#include "file"` - local include, but falls back to system include if `file` is not found.
    fn include(&mut self, start: u32) -> Result<(), Locatable<Error>> {
        use crate::data::lex::ComparisonToken;
        let lexer = self.lexer_mut();
        lexer.consume_whitespace();
        let local = if lexer.match_next(b'"') {
            true
        } else if lexer.match_next(b'<') {
            false
        } else {
            let (id, location) = match self.next_token() {
                Some(Ok(Locatable {
                    data: Token::Id(id),
                    location,
                })) => (id, location),
                Some(Err(err)) => return Err(err),
                Some(Ok(other)) => {
                    return Err(CompileError::new(
                        CppError::UnexpectedToken("include file", other.data).into(),
                        other.location,
                    ))
                }
                None => {
                    return Err(CompileError::new(
                        CppError::EndOfFile("include file").into(),
                        self.span(start),
                    ))
                }
            };
            match self
                .replacer
                .replace(Token::Id(id), location)
                .into_iter()
                .next()
            {
                // local
                Some(Ok(Locatable {
                    data: Token::Literal(Literal::Str(_)),
                    ..
                })) => unimplemented!("#include for macros"), //return self.include_path(id, true, start),
                // system
                Some(Ok(Locatable {
                    data: Token::Comparison(ComparisonToken::Less),
                    ..
                })) => unimplemented!("#include for macros"),
                Some(Err(err)) => return Err(err),
                Some(Ok(other)) => {
                    return Err(CompileError::new(
                        CppError::UnexpectedToken("include file", other.data).into(),
                        other.location,
                    ))
                }
                None => {
                    return Err(CompileError::new(
                        CppError::EndOfFile("include file").into(),
                        self.span(start),
                    ))
                }
            }
        };

        let filename = self.bytes_until(if local { b'"' } else { b'>' });
        self.include_path(filename, local, start)
    }
    // we've done the parsing for an `#include`,
    // now we want to figure what file on disk it corresponds to
    fn find_include_path(
        &mut self,
        filename: String,
        local: bool,
        start: u32,
    ) -> Result<PathBuf, Locatable<Error>> {
        if filename.is_empty() {
            return Err(CompileError::new(
                CppError::EmptyInclude.into(),
                self.span(start),
            ));
        }
        // can't be a closure because of borrowck
        macro_rules! not_found {
            () => {
                Err(CompileError::new(
                    CppError::FileNotFound(filename).into(),
                    self.span(start),
                ))
            };
        }
        // absolute path, ignore everything except the filename
        // e.g `#include </usr/local/include/stdio.h>`
        if filename.as_bytes()[0] == b'/' {
            let path = &std::path::Path::new(&filename);
            return if path.exists() {
                Ok(PathBuf::from(filename))
            } else {
                not_found!()
            };
        }
        // local include: #include "dict.h"
        if local {
            let current_path = &self.files.source(self.lexer().location.file).path;
            let relative_path = &current_path
                .parent()
                .unwrap_or_else(|| std::path::Path::new(""));
            let resolved = relative_path.join(&filename);
            if resolved.exists() {
                return Ok(resolved);
            }
        }
        // if we don't find it locally, we fall back to system headers
        // this is part of the spec! http://port70.net/~nsz/c/c11/n1570.html#6.10.2p3
        for path in &self.search_path {
            let mut buf = PathBuf::from(path.as_ref());
            buf.push(&filename);
            if buf.exists() {
                return Ok(buf);
            }
        }
        return not_found!();
    }
    // we've done the parsing for an `#include`,
    // now we want to do the dirty work of reading it into memory
    fn include_path(
        &mut self,
        filename: Vec<u8>,
        local: bool,
        start: u32,
    ) -> Result<(), Locatable<Error>> {
        // Recall that the original file was valid UTF8.
        // Since in UTF8 no ASCII character can occur
        // within a multi-byte sequence, `filename` must be valid UTF8.
        let filename = String::from_utf8(filename).expect("passed invalid utf8 to start");
        let resolved = self.find_include_path(filename.clone(), local, start)?;
        let src = std::fs::read_to_string(&resolved)
            .map_err(|err| Locatable {
                data: CppError::IO(err.to_string()),
                location: self.span(start),
            })?
            .into();
        let source = crate::Source {
            path: resolved,
            code: Rc::clone(&src),
        };
        let id = self.files.add(filename, source);
        self.includes
            .push(Lexer::new(id, src, self.first_lexer.debug));
        Ok(())
    }
    // Returns every byte between the current position and the next `byte`.
    // Consumes and does not return the final `byte`.
    fn bytes_until(&mut self, byte: u8) -> Vec<u8> {
        let mut bytes = Vec::new();
        loop {
            match self.lexer_mut().next_char() {
                Some(c) if c != byte => bytes.push(c),
                _ => return bytes,
            }
        }
    }
}

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
enum DirectiveKind {
    If,
    IfDef,
    IfNDef,
    Elif,
    Else,
    EndIf,
    Include,
    Define,
    Undef,
    Line,
    Warning,
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
        token.map(CppToken::Token)
    }
}

impl TryFrom<&str> for DirectiveKind {
    type Error = ();
    fn try_from(s: &str) -> Result<Self, ()> {
        use DirectiveKind::*;
        Ok(match s {
            "if" => If,
            "elif" => Elif,
            "endif" => EndIf,
            "else" => Else,
            "ifdef" => IfDef,
            "ifndef" => IfNDef,
            "include" => Include,
            "define" => Define,
            "undef" => Undef,
            "line" => Line,
            "warning" => Warning,
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
    use super::*;
    use crate::data::lex::test::{cpp, cpp_no_newline};

    macro_rules! assert_err {
        ($src: expr, $err: pat, $description: expr $(,)?) => {
            match cpp($src).next().unwrap().unwrap_err().data {
                Error::PreProcessor($err) => {}
                Error::PreProcessor(other) => panic!("expected {}, got {}", $description, other),
                _ => panic!("expected cpp err"),
            }
        };
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
    fn assert_same(src: &str, cpp_src: &str) {
        assert_eq!(
            cpp(src)
                .map(|res| res.map(|token| token.data))
                .collect::<Vec<_>>(),
            cpp(cpp_src)
                .map(|res| res.map(|token| token.data))
                .collect::<Vec<_>>(),
            "{} is not the same as {}",
            src,
            cpp_src,
        );
    }
    #[test]
    fn keywords() {
        for keyword in KEYWORDS.values() {
            // va_list is usually a typedef to `__builtin_va_list`
            // and making it a keyword messes up parsing
            if *keyword != Keyword::VaList {
                println!("{}", keyword);
                assert_keyword(cpp(&keyword.to_string()).next(), *keyword);
            }
        }
    }
    #[test]
    fn if_directive() {
        assert_same(
            "
#if a
    b
#else
    c
#endif",
            "c",
        );
        assert_same(
            "
#if 0 + 2
    b
#endif",
            "b",
        );
        assert_same(
            "
#if 1^1
    b
#endif",
            "",
        );
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

        assert!(cpp("#endif").next().unwrap().is_err());

        let same_line = "#ifdef a #endif\nint main() {}";
        assert!(cpp(same_line).next().unwrap().is_err());
    }
    #[test]
    fn ifndef() {
        let src = "
#ifndef A
#define A
#endif
A";
        assert!(cpp(src).next().is_none());
    }
    #[test]
    fn object_macros() {
        let src = "
#define a b
int a() { return 1; }";
        let cpp_src = "int b() { return 1; }";
        assert_same(src, cpp_src);

        let multidef = "
#define a b + c
int d() { return a; }";
        assert_same(multidef, "int d() { return b + c; }");

        let opdef = "
#define BEGIN {
#define END }
int f() BEGIN return 5; END";
        assert_same(opdef, "int f() { return 5; }");
    }
    #[test]
    fn recursive_macros() {
        assert_same("#define a a\na", "a");
        assert_same("#define a a + b\na", "a + b");
        let mutual_recursion = "
#define a b
#define b a
a";
        assert_same(mutual_recursion, "a");
        let mutual_recursion_2 = "
#define a b
#define b c
#define c a
a";
        assert_same(mutual_recursion_2, "a");
        let mutual_recursion_3 = "
#define a b
#define b c
#define c b
a";
        assert_same(mutual_recursion_3, "b");
        assert_same("#define a \n a", "");
    }
    #[test]
    fn empty_def() {
        assert_err!("#define", CppError::EmptyDefine, "empty define");
        assert_err!(
            "#define
            int",
            CppError::EmptyDefine,
            "empty define",
        );
    }
    #[test]
    fn redefinition() {
        let src = "
#define a b
#define a c
a
";
        assert_same(src, "c");
        let src = "
#define a b
#define a
a
";
        assert_same(src, "");
    }
    #[test]
    fn undef() {
        let src = "
#define a b
a
#undef a
a";
        assert_same(src, "b a");
        let src = "
#define a
#undef a
a
";
        assert_same(src, "a");
    }
    #[test]
    fn else_directive() {
        use super::CppError;
        let src = "
#if 1
#if 0
b
#else
// this should be an error
#else
d
#endif
";
        assert_err!(src, CppError::UnexpectedElse, "duplicate else",);
    }
    #[test]
    fn elif() {
        let src = "
            #define __WORDSIZE 64
            #if 0
                wrong1
            #elif __WORDSIZE == 64
                right
            #else
                wrong2
            #endif
        ";
        assert_same(src, "right");
    }
    #[test]
    fn function_body_replacement() {
        let src = "#define a b
        #define f(c) a
        f(1)";
        assert_same(src, "b")
    }
    #[test]
    fn object_body_replacement() {
        let src = "#define NULL ((void*)0)
        int *p = NULL;";
        assert_same(src, "int *p = ((void*)0);")
    }
    #[test]
    fn pragma() {
        let src = "#pragma gcc __attribute__((inline))";
        assert!(cpp(src).next().is_none());
    }
    #[test]
    fn line() {
        let src = "#line 1";
        let mut cpp = cpp(src);
        assert!(cpp.next().is_none());
        assert!(cpp.warnings().pop_front().is_some());
    }
    #[test]
    fn warning() {
        let src = "#warning your pants are on file";
        let mut cpp = cpp(src);
        assert!(cpp.next().is_none());
        assert!(cpp.warnings().pop_front().is_some());
    }
    #[test]
    fn error() {
        assert_err!("#error cannot drink and drive", CppError::User(_), "#error",);
    }
    #[test]
    fn invalid_directive() {
        assert_err!("#wrong", CppError::InvalidDirective, "invalid directive",);
        assert_err!("#1", CppError::UnexpectedToken(_, _), "unexpected token",);
        assert_err!("#include", CppError::EndOfFile(_), "end of file");
        assert_err!("#if defined", CppError::EndOfFile(_), "end of file");
        for s in &[
            "#if defined()",
            "#if defined(+)",
            "#if defined)",
            "#if defined(()",
            "#if defined(a a",
        ] {
            assert_err!(s, CppError::UnexpectedToken(_, _), "unexpected token");
        }
        assert_err!("#if", CppError::EmptyExpression, "empty expression");
    }
    #[test]
    // make sure that `"b"` doesn't accidentally consume the newline token
    // without resetting `self.seen_line_token`
    fn str_at_eol() {
        let src = r#"
#define a "b"
#define c a
c
"#;
        assert_same(src, "\"b\"");
    }
    #[test]
    fn test_comment_newline() {
        let tokens: Vec<_> = cpp_no_newline(
            "
#if 1 //
int main() {}
#endif
",
        )
        .collect();
        assert_eq!(tokens, cpp("int main() {}").collect::<Vec<_>>());
        assert_same(
            "
#if 1 /**//**/
int main(){}
#endif
",
            "int main() {}",
        );
    }
    #[test]
    fn cycle_detection() {
        let src = "
        #define sa_handler   __sa_handler.sa_handler
        s.sa_handler";
        assert_same(src, "s.__sa_handler.sa_handler");
    }
    #[test]
    fn parens() {
        let original = "#define f(a, b) a\nf((1, 2, 3), 2)";
        let expected = "(1, 2, 3)";
        assert_same(original, expected);

        let original = "#define foo(x, y) { x, y }\nfoo(5 (6), 7)";
        let expected = "{ 5 (6), 7 }";
        assert_same(original, expected);

        let original = "#define f(a, b, c) a + b + c\nf((((1))), ((2)), (3))";
        let expected = "(((1))) + ((2)) + (3)";
        assert_same(original, expected);
    }
    #[test]
    fn recursive_function() {
        let original = "#define f(a) f(a + 1)\nf(1)";
        let expected = "f(1 + 1)";
        assert_same(original, expected);
    }
    #[test]
    // https://github.com/jyn514/rcc/issues/427
    fn mutually_recursive_function() {
        let original = "
            #define a(c) b(c)
            #define b(c) a(c)
            a(1)
        ";
        assert_same(original, "a(1)");
    }
}
