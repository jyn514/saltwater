//! The preprocessor is made of 2 nested iterators:
//!
//! 1. The innermost iterator (`FileProcessor`) deals with multiple files/lexers.
//!    If one included file runs out of tokens, it seamlessly goes on to the next one.
//! 2. The outermost iterator (`PreProcessor`) deals with preprocessing directives.
//!    Additionally, because of the weird way I lumped the lexer and preprocessor together,
//!    it recognizes keywords and turns `Token::Id` into `Token::Keyword` as necessary.
//!
//! There is also a step in the middle to preform macro replacement.
//! The `PreProcessor` sometimes does not want to replace its tokens (e.g. for `#if defined(a)`).
//! In this case, it reaches directly into the `FileProcessor` to drag out those tokens.
//! Because of this, the macro processor cannot have any idea of pending tokens,
//! or its `pending` will conflict with the `PreProcessor`'s `pending`.
//! This is the origin of the `inner` argument to `replace()`.
//!
//! This supports inputs other than `FileProcessor`,
//! but at the same time the `MacroReplacer` needs to be able to peek ahead in the input
//! to see whether a token defined as a function macro is followed by a `(`.
//! To support both these use cases, I create a new trait called `Peekable`;
//! the intent is that users of saltwater can use arbitrary iterators over `Token` by calling `iter.peekable()`.
//!
//! TODO: The `PreProcessor` is very tightly coupled to the `FileProcessor`.
//!
//! This is the file for the `PreProcessor`.

use lazy_static::lazy_static;

use arcstr::{ArcStr, Substr};
use std::borrow::Cow;
use std::collections::{HashMap, VecDeque};
use std::convert::TryFrom;
use std::path::{Path, PathBuf};

use super::files::FileProcessor;
use super::replace::{replace, replace_iter, Definition, Definitions};
use super::{Lexer, LiteralParser, Token};
use crate::arch::TARGET;
use crate::data::error::CppError;
use crate::data::lex::{Keyword, LiteralToken};
use crate::data::*;
use crate::get_str;
use crate::Files;

/// An easier interface for constructing a preprocessor.
///
/// Here is the example for `PreProcessor::new()` using the builder:
/// ```
/// use saltwater_parser::PreProcessorBuilder;
///
/// let cpp = PreProcessorBuilder::new("int main(void) { char *hello = \"hi\"; }\n").filename("example.c").build();
/// for token in cpp {
///     assert!(token.is_ok());
/// }
/// ```
pub struct PreProcessorBuilder<'a> {
    /// The buffer for the starting file
    buf: ArcStr,
    /// The name of the file
    filename: PathBuf,
    /// Whether to print each token before replacement
    debug: bool,
    /// The paths to search for `#include`d files
    search_path: Vec<Cow<'a, Path>>,
    /// The user-defined macros that should be defined at startup
    definitions: Definitions,
}

impl<'a> PreProcessorBuilder<'a> {
    pub fn new<S: Into<ArcStr>>(buf: S) -> PreProcessorBuilder<'a> {
        PreProcessorBuilder {
            debug: false,
            filename: PathBuf::default(),
            buf: buf.into(),
            search_path: Vec::new(),
            definitions: Definitions::new(),
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
/// use saltwater_parser::PreProcessor;
///
/// let cpp = PreProcessor::new("int main(void) { char *hello = \"hi\"; }\n", "example.c", false, vec![], Default::default());
/// for token in cpp {
///     assert!(token.is_ok());
/// }
/// ```
pub struct PreProcessor<'a> {
    error_handler: ErrorHandler,
    /// Keeps track of current `#if` directives
    nested_ifs: Vec<IfState>,
    /// The tokens that have been `#define`d and are currently being substituted
    pending: VecDeque<Locatable<PendingToken>>,
    /// The paths to search for `#include`d files
    search_path: Vec<Cow<'a, Path>>,
    /// The current macro definitions
    definitions: Definitions,
    /// Handles reading from files
    file_processor: FileProcessor,
}

enum PendingToken {
    Replaced(Token),
    NeedsReplacement(Token),
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
        let value = arcstr::format!("{}\n", value);
        let mut files = codespan::Files::new();
        let dummy_id = files.add("<impl TryFrom<&str> for Definition>", ArcStr::clone(&value));
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
                        CppToken::Token(token) => {
                            self.handle_token(PendingToken::NeedsReplacement(token), loc.location)
                        }
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

fn now_local() -> time::OffsetDateTime {
    match time::OffsetDateTime::try_now_local() {
        Ok(ok) => ok,
        Err(_) => time::OffsetDateTime::now_utc(),
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
    /// Possibly recursively replace tokens. This also handles turning identifiers into keywords.
    ///
    /// If `token` was defined to an empty token list, this will return `None`.
    fn handle_token(
        &mut self,
        token: PendingToken,
        location: Location,
    ) -> Option<CppResult<Token>> {
        let mut token = {
            // if we've already replaced the token once, don't do it again
            // avoids infinite loops on cyclic defines (#298)
            match token {
                PendingToken::Replaced(t) => Some(Ok(Locatable::new(t, location))),
                PendingToken::NeedsReplacement(token) => {
                    self.update_builtin_definitions();
                    let mut replacement_list =
                        replace(&self.definitions, token, &mut self.file_processor, location)
                            .into_iter();
                    let first = replacement_list.next();
                    for remaining in replacement_list {
                        match remaining {
                            Err(err) => self.error_handler.push_back(err),
                            Ok(token) => self.pending.push_back(token.map(PendingToken::Replaced)),
                        }
                    }
                    first
                }
            }
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
    }

    /// Create a new preprocessor for the file identified by `file`.
    ///
    /// Note that the preprocessor may add arbitrarily many `#include`d files to `files`,
    /// but will never delete a file.
    ///
    /// The `debug` parameter specifies whether to print out tokens before replacement.
    pub fn new<'search: 'a, I: IntoIterator<Item = Cow<'search, Path>>, S: Into<ArcStr>>(
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

        let now = now_local();

        #[allow(clippy::inconsistent_digit_grouping)]
        let mut definitions = map! {
            format!("__{}__", TARGET.architecture).into() => int_def(1),
            format!("__{}__", TARGET.operating_system).into() => int_def(1),
            "__STDC__".into() => int_def(1),
            "__STDC_HOSTED__".into() => int_def(1),
            "__STDC_VERSION__".into() => int_def(2011_12),
            "__STDC_NO_ATOMICS__".into() => int_def(1),
            "__STDC_NO_COMPLEX__".into() => int_def(1),
            "__STDC_NO_THREADS__".into() => int_def(1),
            "__STDC_NO_VLA__".into() => int_def(1),
            "__DATE__".into() => str_def(&now.format("%b %_d %Y")),
            "__TIME__".into() => str_def(&now.format("%H:%M:%S")),
        };
        definitions.extend(user_definitions);
        let mut search_path = vec![
            PathBuf::from(format!("/usr/local/include/{}", system_path)).into(),
            Path::new("/usr/local/include").into(),
            PathBuf::from(format!("/usr/include/{}", system_path)).into(),
            Path::new("/usr/include").into(),
        ];
        search_path.extend(user_search_path.into_iter());

        let file_processor = FileProcessor::new(chars, filename, debug);

        let mut new_cpp = Self {
            error_handler: Default::default(),
            nested_ifs: Default::default(),
            pending: Default::default(),
            search_path,
            definitions,
            file_processor,
        };
        new_cpp.update_builtin_definitions(); // So they are defined from the start
        new_cpp
    }

    /// Return all warnings found so far.
    ///
    /// These warnings are consumed and will not be returned if you call
    /// `warnings()` again.
    pub fn warnings(&mut self) -> VecDeque<CompileWarning> {
        let mut warnings = std::mem::take(&mut self.error_handler.warnings);
        warnings.extend(std::mem::take(
            &mut self.file_processor.error_handler.warnings,
        ));
        warnings
    }

    pub fn eof(&self) -> Location {
        self.file_processor.eof()
    }

    pub fn into_files(self) -> Files {
        self.file_processor.into_files()
    }

    /* internal functions */
    fn span(&self, start: u32) -> Location {
        self.file_processor.span(start)
    }

    fn lexer(&mut self) -> &Lexer {
        self.file_processor.lexer()
    }

    fn lexer_mut(&mut self) -> &mut Lexer {
        self.file_processor.lexer_mut()
    }

    fn line(&self) -> usize {
        self.file_processor.line()
    }

    fn tokens_until_newline(&mut self, whitespace: bool) -> Vec<CompileResult<Locatable<Token>>> {
        self.file_processor.tokens_until_newline(whitespace)
    }

    fn is_whitespace(res: &CppResult<Token>) -> bool {
        matches!(
            res,
            Ok(Locatable {
                data: Token::Whitespace(_),
                ..
            })
        )
    }
    fn is_not_whitespace(res: &CppResult<Token>) -> bool {
        !PreProcessor::is_whitespace(res)
    }

    /// If at the start of the line and we see `#directive`, return that directive.
    /// Otherwise, if we see a token (or error), return that error.
    /// Otherwise, return `None`.
    fn next_cpp_token(&mut self) -> Option<CppResult<CppToken>> {
        let next_token = self.file_processor.next()?;
        let is_hash = match next_token {
            Ok(Locatable {
                data: Token::Hash, ..
            }) => true,
            _ => false,
        };
        Some(if is_hash && !self.file_processor.seen_line_token() {
            let line = self.file_processor.line();
            match self.file_processor.next_non_whitespace()? {
                Ok(Locatable {
                    data: Token::Id(id),
                    location,
                }) if self.file_processor.line() == line => {
                    if let Ok(directive) = DirectiveKind::try_from(get_str!(id)) {
                        Ok(Locatable::new(CppToken::Directive(directive), location))
                    } else {
                        Err(Locatable::new(CppError::InvalidDirective.into(), location))
                    }
                }
                Ok(other) => {
                    if self.file_processor.line() == line {
                        Err(other.map(|tok| CppError::UnexpectedToken("directive", tok).into()))
                    } else {
                        Ok(other.into())
                    }
                }
                other => other.map(Locatable::from),
            }
        } else {
            next_token.map(Locatable::from)
        })
    }
    // this function does _not_ perform macro substitution
    fn expect_id(&mut self) -> CppResult<InternedStr> {
        let location = self.file_processor.span(self.file_processor.offset());
        match self.file_processor.next() {
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
                self.consume_whitespace_oneline(start, CppError::ExpectedMacroId)?;
                let name = self.expect_id()?;
                self.if_directive(!self.definitions.contains_key(&name.data), start)
            }
            IfDef => {
                self.consume_whitespace_oneline(start, CppError::ExpectedMacroId)?;
                let name = self.expect_id()?;
                self.if_directive(self.definitions.contains_key(&name.data), start)
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
                self.consume_whitespace_oneline(start, CppError::EmptyExpression)?;
                let name = self.expect_id()?;
                self.definitions.remove(&name.data);
                Ok(())
            }
            Pragma => {
                self.error_handler
                    .warn(WarningDiagnostic::IgnoredPragma, self.span(start));
                drop(self.tokens_until_newline(false));
                Ok(())
            }
            // NOTE: #warning is a non-standard extension, but is implemented
            // by most major compilers including clang and gcc.
            Warning => {
                let tokens: Vec<_> = self
                    .tokens_until_newline(false)
                    .into_iter()
                    .map(|res| res.map(|l| l.data))
                    .collect::<Result<_, _>>()?;
                self.error_handler
                    .warn(WarningDiagnostic::User(tokens), self.span(start));
                Ok(())
            }
            Error => {
                let tokens: Vec<_> = self
                    .tokens_until_newline(false)
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
                drop(self.tokens_until_newline(false));
                Ok(())
            }
            Include => self.include(start),
        }
    }
    // convienience function around cpp_expr
    fn boolean_expr(&mut self) -> Result<bool, CompileError> {
        let start = self.file_processor.offset();
        let lex_tokens: Vec<_> = self
            .tokens_until_newline(false)
            .into_iter()
            .collect::<Result<_, CompileError>>()?;
        let location = self.span(start);

        self.update_builtin_definitions();
        // TODO: is this unwrap safe? there should only be scalar types in a cpp directive...
        match Self::cpp_expr(&self.definitions, lex_tokens.into_iter(), location)?
            .truthy(&mut self.error_handler)
            .constexpr()?
            .data
        {
            (LiteralValue::Int(i), Type::Bool) => Ok(i != 0),
            _ => unreachable!("bug in const_fold or parser: cpp cond should be boolean"),
        }
    }
    // `#if defined(a)` or `#if defined a`
    // http://port70.net/~nsz/c/c11/n1570.html#6.10.1p1
    fn defined(
        mut lex_tokens: impl Iterator<Item = Locatable<Token>>,
        location: Location,
    ) -> Result<InternedStr, CompileError> {
        enum State {
            Start,
            SawParen,
            SawId(InternedStr),
        }
        use State::*;
        let mut state = Start;
        loop {
            return match lex_tokens.next() {
                None => Err(CompileError::new(
                    CppError::EndOfFile("defined(identifier)").into(),
                    location,
                )),
                Some(Locatable {
                    data: Token::Id(def),
                    location,
                }) => match state {
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
                Some(Locatable {
                    data: Token::LeftParen,
                    location,
                }) => match state {
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
                Some(Locatable {
                    data: Token::RightParen,
                    location,
                }) => match state {
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
                Some(other) => Err(CompileError::new(
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
    pub fn cpp_expr<L>(
        definitions: &Definitions,
        mut lex_tokens: L,
        location: Location,
    ) -> CompileResult<hir::Expr>
    where
        L: Iterator<Item = Locatable<Token>>,
    {
        const ONE: LiteralToken = LiteralToken::Int(arcstr::literal_substr!("1"));
        const ZERO: LiteralToken = LiteralToken::Int(arcstr::literal_substr!("0"));

        let mut cpp_tokens = Vec::with_capacity(lex_tokens.size_hint().1.unwrap_or_default());
        let defined = "defined".into();

        while let Some(token) = lex_tokens.next() {
            let token = match token {
                // #if defined(a)
                Locatable {
                    data: Token::Id(name),
                    location,
                } if name == defined => {
                    let def = Self::defined(&mut lex_tokens, location)?;
                    let literal = if definitions.contains_key(&def) {
                        ONE
                    } else {
                        ZERO
                    };
                    location.with(Token::Literal(literal))
                }
                _ => token,
            };
            cpp_tokens.push(token);
        }
        let mut expr_location = None;
        let cpp_tokens: Vec<_> = replace_iter(cpp_tokens.into_iter().map(Result::Ok), definitions)
            .flatten()
            .filter(PreProcessor::is_not_whitespace)
            .map(|mut token| {
                if let Ok(tok) = &mut token {
                    expr_location = Some(location.maybe_merge(expr_location));
                    if let Token::Id(_) = tok.data {
                        tok.data = Token::Literal(ZERO);
                    }
                }
                token
            })
            .collect();
        if cpp_tokens.is_empty() {
            return Err(CompileError::new(
                CppError::EmptyExpression.into(),
                location,
            ));
        }
        // TODO: this only returns the first error because anything else requires a refactor
        use crate::{analyze::PureAnalyzer, Parser};
        let mut parser = Parser::new(cpp_tokens.into_iter(), false);
        let expr = parser.expr()?;
        if !parser.is_empty() {
            return Err(CompileError::new(
                CppError::TooManyTokens.into(),
                expr_location.unwrap(),
            ));
        }
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
            match self.file_processor.next_non_whitespace() {
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
                })) => {
                    let location = self.lexer().span(start);
                    self.error_handler
                        .warn(crate::data::error::Warning::IgnoredVariadic, location);
                }
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
            self.consume_whitespace_oneline(
                self.file_processor.offset(),
                CppError::Expected("',' or ')'", "macro parameter list"),
            )?;
            // either `,` or `)`
            if self.lexer_mut().match_next(')') {
                return Ok(arguments);
            }
            if self.lexer_mut().match_next(',') {
                continue;
            }
            // some other token
            match self.file_processor.next() {
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
            this.tokens_until_newline(true)
                .into_iter()
                .skip_while(PreProcessor::is_whitespace)  // TODO warning if nothing skips
                .map(|res| res.map(|loc| loc.data))
                .collect::<Result<Vec<_>, Locatable<Error>>>()
        };

        self.consume_whitespace_oneline(start, CppError::EmptyDefine)?;
        let id = self.expect_id()?;
        // NOTE: does _not_ discard whitespace
        if self.lexer_mut().match_next('(') {
            // function macro
            // first, parse the arguments:
            // # define identifier lparen identifier-listopt ) replacement-list new-line
            // # define identifier lparen ... ) replacement-list new-line
            // # define identifier lparen identifier-list , ... ) replacement-list new-line
            self.consume_whitespace_oneline(
                self.file_processor.offset(),
                CppError::Expected(")", "macro parameter list"),
            )?;
            let params = if !self.lexer_mut().match_next(')') {
                self.fn_args(start)?
            } else {
                Vec::new()
            };
            let body = body(self)?;
            self.define_macro(id.data, Definition::Function { params, body })
                .map_err(|e| self.span(start).with(e))?;
            Ok(())
        } else {
            // object macro
            let tokens = body(self)?;
            self.define_macro(id.data, Definition::Object(tokens))
                .map_err(|e| self.span(start).with(e))?;
            Ok(())
        }
    }
    fn define_macro(&mut self, name: InternedStr, definition: Definition) -> Result<(), CppError> {
        use std::collections::hash_map::Entry;
        match self.definitions.entry(name) {
            Entry::Vacant(entry) => {
                entry.insert(definition);
                Ok(())
            }
            Entry::Occupied(entry) => {
                // This behavior is defined by the spec in section 6.10.3p1
                if entry.get() != &definition {
                    Err(CppError::IncompatibleRedefinition(name))
                } else {
                    Ok(())
                }
            }
        }
    }
    // http://port70.net/~nsz/c/c11/n1570.html#6.10.2
    // `#include <file>` - system include
    // `#include "file"` - local include, but falls back to system include if `file` is not found.
    fn include(&mut self, start: u32) -> Result<(), Locatable<Error>> {
        use crate::data::lex::ComparisonToken;
        self.consume_whitespace_oneline(start, CppError::EmptyInclude)?;
        let lexer = self.lexer_mut();
        let local = if lexer.match_next('"') {
            true
        } else if lexer.match_next('<') {
            false
        } else {
            let (id, location) = match self.file_processor.next() {
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
            self.update_builtin_definitions();
            match replace(
                &self.definitions,
                Token::Id(id),
                &mut self.file_processor,
                location,
            )
            .into_iter()
            .next()
            {
                // local
                Some(Ok(Locatable {
                    data: Token::Literal(LiteralToken::Str(_)),
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

        let end = if local { '"' } else { '>' };
        let filename = PathBuf::from(self.chars_until(end).to_owned());
        self.include_path(filename, local, start)
    }
    // we've done the parsing for an `#include`,
    // now we want to figure what file on disk it corresponds to
    fn find_include_path(
        &mut self,
        filename: &Path,
        local: bool,
        start: u32,
    ) -> Result<PathBuf, Locatable<Error>> {
        if filename.as_os_str().is_empty() {
            return Err(CompileError::new(
                CppError::EmptyInclude.into(),
                self.span(start),
            ));
        }

        let not_found = |this: &Self, filename: &Path| {
            Err(this.span(start).error(CppError::FileNotFound(
                filename.to_string_lossy().to_string(),
            )))
        };

        // absolute path, ignore everything except the filename
        // e.g `#include </usr/local/include/stdio.h>`
        if filename.is_absolute() {
            return if filename.exists() {
                Ok(filename.to_owned())
            } else {
                not_found(self, filename)
            };
        }
        // local include: #include "dict.h"
        if local {
            let current_path = self.file_processor.path();
            let relative_path = &current_path
                .parent()
                .unwrap_or_else(|| std::path::Path::new(""));
            let resolved = relative_path.join(filename);
            if resolved.exists() {
                return Ok(resolved);
            }
        }
        // if we don't find it locally, we fall back to system headers
        // this is part of the spec! http://port70.net/~nsz/c/c11/n1570.html#6.10.2p3
        for path in &self.search_path {
            let mut buf = path.clone().into_owned();
            buf.push(filename);
            if buf.exists() {
                return Ok(buf);
            }
        }

        not_found(self, filename)
    }
    // we've done the parsing for an `#include`,
    // now we want to do the dirty work of reading it into memory
    fn include_path(
        &mut self,
        filename: PathBuf,
        local: bool,
        start: u32,
    ) -> Result<(), Locatable<Error>> {
        let (path, src) = match self.find_include_path(&filename, local, start) {
            Ok(path) => {
                let src = std::fs::read_to_string(&path)
                    .map_err(|err| Locatable {
                        data: CppError::IO(err.to_string()),
                        location: self.span(start),
                    })?
                    .into();
                (path, src)
            }
            Err(not_found) => {
                let filename = match filename.file_name().and_then(|f| f.to_str()) {
                    None => return Err(not_found),
                    Some(f) => f,
                };
                match get_builtin_header(filename) {
                    Some(file) => {
                        let mut path = PathBuf::from("<builtin>");
                        path.push(filename);
                        (path, ArcStr::from(file))
                    }
                    None => return Err(not_found),
                }
            }
        };
        let source = crate::Source {
            path,
            code: ArcStr::clone(&src),
        };
        self.file_processor.add_file(filename, source);
        Ok(())
    }
    /// Returns every char between the current position and the next `end`.
    /// Consumes and does not return the final `end`.
    fn chars_until(&mut self, end: char) -> &str {
        // directives must not span multiple files
        let lexer = self.file_processor.lexer_mut();
        let offset = lexer.location.offset as usize;
        match lexer.chars[offset..].find(end) {
            None => {
                lexer.location.offset += (lexer.chars.len() - offset) as u32;
                &lexer.chars[offset..]
            }
            Some(idx) => {
                lexer.location.offset += idx as u32;
                let s = &lexer.chars[offset..lexer.location.offset as usize];
                lexer.location.offset += 1; // to account for `end`
                s
            }
        }
    }

    /// Returns next token in stream which is not whitespace
    pub fn next_non_whitespace(&mut self) -> Option<CppResult<Token>> {
        loop {
            match self.next() {
                Some(Ok(Locatable {
                    data: Token::Whitespace(_),
                    ..
                })) => continue,
                other => break other,
            }
        }
    }

    /// Consumes whitespace but returns error if it includes a newline
    #[inline]
    fn consume_whitespace_oneline(
        &mut self,
        start: u32,
        error: CppError,
    ) -> Result<String, CompileError> {
        let line = self.line();
        let ret = self.file_processor.consume_whitespace();
        if self.line() != line {
            return Err(self.span(start).error(error));
        }
        Ok(ret)
    }

    fn update_builtin_definitions(&mut self) {
        self.definitions.extend(map! {
            "__LINE__".into() => int_def((self.line() + 1) as i32),
            "__FILE__".into() => str_def(self.file_processor.path().to_string_lossy()),
        })
    }
}

fn int_def(i: i32) -> Definition {
    Definition::Object(vec![LiteralToken::Int(Substr::from(i.to_string())).into()])
}
fn str_def<S: Into<String>>(s: S) -> Definition {
    let substr = Substr::from(arcstr::format!("\"{}\"", s.into().replace(r#"""#, r#"\""#)));
    Definition::Object(vec![LiteralToken::Str(vec![substr]).into()])
}

macro_rules! built_in_headers {
    ( $($filename: literal),+ $(,)? ) => {
        [
            // Relative to the current file, not the crate root
            $( ($filename, include_str!(concat!(env!("CARGO_MANIFEST_DIR"), "/headers/", $filename))) ),+
        ]
    };
}

// [(filename, contents)]
// TODO: this could probably use a perfect-hashmap,
// but it's so small that it's not worth it
const PRECOMPILED_HEADERS: [(&str, &str); 2] = built_in_headers! {
    "stdarg.h",
    "stddef.h",
};

fn get_builtin_header(expected: impl AsRef<str>) -> Option<&'static str> {
    PRECOMPILED_HEADERS
        .iter()
        .find(|&(path, _)| path == &expected.as_ref())
        .map(|x| x.1)
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
            match cpp($src).next_non_whitespace().unwrap().unwrap_err().data {
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
    fn is_same_preprocessed(xs: PreProcessor, ys: PreProcessor) -> bool {
        let to_vec = |xs: PreProcessor| {
            xs.filter(PreProcessor::is_not_whitespace)
                .map(|res| res.map(|token| token.data))
                .collect::<Vec<_>>()
        };
        to_vec(xs) == to_vec(ys)
    }
    fn assert_same(src: &str, cpp_src: &str) {
        assert!(
            is_same_preprocessed(cpp(src), cpp(cpp_src)),
            "{} is not the same as {}",
            src,
            cpp_src,
        );
    }
    fn assert_same_exact(src: &str, cpp_src: &str) {
        // NOTE make sure `cpp_src` has a trailing newline
        let pprint = cpp(src)
            .filter_map(|res| res.ok().map(|token| token.data.to_string()))
            .collect::<Vec<_>>()
            .join("");
        assert_eq!(pprint, format!("{}\n", cpp_src)); // Because `cpp` adds newline, do it here too
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
    fn if_fn_directive() {
        assert_same(
            "
#define f(a) 1
#if f(a)
success
#endif",
            "success",
        );
        assert_same(
            "
#define f(a) a*a
#define g(a) 2*a
#define h(b, c) 3*b + 4*c
#if f(5) == g(0) + h(1, 2)
failure
#elif f(5) == g(6) + h(3, 1)
success
#endif",
            "success",
        );
    }
    #[test]
    fn ifdef() {
        let code = "#ifdef a
        whatever, doesn't matter
        #endif";
        assert_eq!(cpp(code).next_non_whitespace(), None);

        let code = "#ifdef a\n#endif";
        assert_eq!(cpp(code).next_non_whitespace(), None);

        assert!(cpp("#ifdef").next_non_whitespace().unwrap().is_err());

        let nested = "#ifdef a
        #ifdef b
        int main() {}
        #endif
        #endif
        char;";
        assert_eq!(
            cpp(nested).next_non_whitespace().unwrap().unwrap().data,
            Token::Keyword(Keyword::Char)
        );

        assert!(cpp("#endif").next_non_whitespace().unwrap().is_err());

        let same_line = "#ifdef a #endif\nint main() {}";
        assert!(cpp(same_line).next_non_whitespace().unwrap().is_err());
    }
    #[test]
    fn ifndef() {
        let src = "
#ifndef A
#define A
#endif
A";
        assert!(cpp(src).next_non_whitespace().is_none());
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
        assert_err!(
            src,
            CppError::IncompatibleRedefinition(_),
            "incompatible redfinition"
        );
        let src = "
#define a b
#define a
a
";
        assert_err!(
            src,
            CppError::IncompatibleRedefinition(_),
            "incompatible redefinition"
        );

        let src = "
#define a b
#define a b
a
";
        assert_same(src, "b");

        let src = "
#define a(b) b+1
#define a(b) b+2
a(2)
";
        assert_err!(
            src,
            CppError::IncompatibleRedefinition(_),
            "incompatible redefinition"
        );

        let src = "
#define a(b) b+1
#define a(c) c+1
a(2)
";
        assert_err!(
            src,
            CppError::IncompatibleRedefinition(_),
            "incompatible redefinition"
        );

        let src = "
#define a(b) b+1
#define a(b) b+1
a(2)
";
        assert_same(src, "2+1");
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
        assert!(cpp(src).next_non_whitespace().is_none());
    }
    #[test]
    fn line() {
        let src = "#line 1";
        let mut cpp = cpp(src);
        assert!(cpp.next_non_whitespace().is_none());
        assert!(cpp.warnings().pop_front().is_some());
    }
    #[test]
    fn warning() {
        let src = "#warning your pants are on file";
        let mut cpp = cpp(src);
        assert!(cpp.next_non_whitespace().is_none());
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
        assert_err!("#include", CppError::EmptyInclude, "empty include");
        assert_err!("#if defined", CppError::EndOfFile(_), "unexpected eof");
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
        let tokens = cpp_no_newline(
            "
#if 1 //
int main() {}
#endif
",
        );
        assert!(is_same_preprocessed(tokens, cpp("int main() {}")));
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
    #[test]
    // https://github.com/jyn514/rcc/issues/356
    fn preprocess_only() {
        let assert_unchanged = |s| assert_same_exact(s, s);
        assert_unchanged("\"abc\\?\" 1 2.0 3.000f 0x88 false");
        assert_unchanged("sdflasd;lfja s;dkj;adjsfl;ds lkjl;jljlkj23840uofjsd;");
        assert_unchanged("int \t\n\r     main() {}");
        assert_same_exact("int/* */main() {}", "int main() {}");
        assert_same_exact("int/*\n\n\n*/main() {}", "int\n\n\nmain() {}");
        assert_same_exact("#define a(c) c\tc\na(1);a(2)", "\n1 1;2 2");
        assert_same_exact("#define a //\n#if defined a\n  x\n#endif", "\n\n  x\n");
        assert_same_exact("#define x\n#undef x\n  x", "\n\n  x");
        assert_same_exact("#pragma once\n  x", "\n  x");
        assert_same_exact("#warning dont panic\n  x", "\n  x");
        assert_same_exact("#error dont panic\n  x", "\n  x");
        assert_same_exact("#line 1\n  x", "\n  x");
        assert_same_exact(
            "---
#define a
---
#if 1
  x
  y
  z
#endif
---
#if 0
  x
#endif
---
#ifdef a
  x
#endif
---
#ifndef a
  x
#endif
---",
            "---

---

  x
  y
  z

---

---

  x

---

---",
        );
        // TODO test for #includes
    }

    #[test]
    fn space_separated_function_macro() {
        assert_same_exact("#define f(a) <a>\nf     (a)", "\n<a>");
        assert_same_exact("#define f(a) <a>\nf(a)", "\n<a>");
        assert_same_exact("#define f(a) <a>\nf", "\nf");
        assert_same_exact("#define f(a) <a>\nf   ", "\nf   ");
        assert_same_exact("#define f(a) <a>\nf   ;", "\nf   ;");
        assert_same_exact("#define f(a) <a>\nf;", "\nf;");
        assert_same_exact(
            "#define f(a) 1
#define h f (2)
h",
            "\n\n1",
        );
    }

    #[test]
    fn eof_after_macro_call() {
        use crate::data::lex::test::cpp_no_newline;

        let cpp = cpp_no_newline("#define f(a)\nf")
            .filter_map(|res| res.ok().map(|token| token.data.to_string()))
            .collect::<Vec<_>>()
            .join("");
        assert_eq!(cpp, "\nf");
    }
    fn assert_same_stringified(cpp: &str, cpp_src: &str) {
        assert_same_exact(
            &format!("#define xstr(a) #a\nxstr({})", cpp),
            &format!("\n{}", cpp_src),
        );
    }
    #[test]
    fn stringify() {
        assert_same_stringified("a + b", r#""a + b""#);
        assert_same_stringified(r#"b   	 +"c""#, r#""b +\"c\"""#);
        assert_same_stringified(r#""+\\+\n+\"+""#, r#""\"+\\\\+\\n+\\\"+\"""#);
        assert_same_exact("#define xstr(a, b) #a = b\nxstr(1+2,3)", "\n\"1+2\" = 3");
        assert_same_exact("#define xstr(a, b) a b\nxstr(1+2,3)", "\n1+2 3");
        assert_same_exact("#define xstr(a) # a\nxstr(1+2)", "\n\"1+2\"");
        assert_same_exact("#define hash #a\nhash", "\n#a");

        assert_same_stringified(r#""\'""#, r#""\"\\'\"""#);
        assert_same_stringified(r#""	""#, r#""\"	\"""#); // Tab in string should be maintained
        assert_same_stringified(
            r#""\a+\b+\e+\f+\r+\v+\?""#,
            r#""\"\\a+\\b+\\e+\\f+\\r+\\v+\\?\"""#,
        );
        assert_same_stringified(r#""\x3f""#, r#""\"\\x3f\"""#);
        assert_same_stringified(r#""\xff""#, r#""\"\\xff\"""#);

        assert_same_stringified(r#"'\n'"#, r#""'\\n'""#);
        assert_same_stringified(r#"  a +   b"#, r#""a + b""#);
        assert_same_stringified("", r#""""#);
        assert_same_exact(
            r#"#define f(  x  ,y  )   4 # x ; #y
          f (   42 ,  "hey there world" ) + f(1,0) "#,
            r#"
          4 "42" ; "\"hey there world\"" + 4 "1" ; "0" "#,
        );
        assert!(cpp("#define f(x) #y\nf(0)").any(|x| x.is_err()));
        assert!(cpp("#define f(x) #+\nf(0)").any(|x| x.is_err()));
    }

    #[test]
    fn builtins_line() {
        assert_same("__LINE__", "1");
        assert_same("\n\n\n\n\n\n\n\n\n__LINE__", "10");
        assert_same(
            "#ifdef __LINE__
            1
            #endif",
            "1",
        );
        assert_same(
            "
            
            #if __LINE__ == 3
            1
            #endif",
            "1",
        );
        assert_same(
            "#define LINE __LINE__
            
            
            LINE",
            "4",
        );
        assert_same(
            "__LINE__
            __LINE__
            __LINE__

            __LINE__",
            "1 2 3 5",
        );
    }
    #[test]
    fn builtins_file() {
        let filename = "helloworld.c";
        let mut cpp = PreProcessorBuilder::new("__FILE__")
            .filename(filename)
            .build();
        let token = cpp.next_non_whitespace().unwrap().unwrap().data;
        if let Token::Literal(LiteralToken::Str(rcstrs)) = token {
            assert_eq!(
                rcstrs.first().unwrap().as_str(),
                format!("\"{}\"", filename)
            );
        } else {
            panic!();
        }
    }
    #[test]
    fn builtins_date_time() {
        use time::OffsetDateTime;
        fn assert_same_datetime(src: &str, cpp_src: &str, datetime: OffsetDateTime) {
            let mut preprocessor = PreProcessorBuilder::new(src).build();
            preprocessor.definitions.extend(map! {
                "__DATE__".into() => str_def(&datetime.format("%b %_d %Y")),
                "__TIME__".into() => str_def(&datetime.format("%H:%M:%S")),
            });
            assert!(
                is_same_preprocessed(preprocessor, cpp(cpp_src)),
                "{} is not the same as {}",
                src,
                cpp_src,
            );
        }

        fn assert_is_str(src: &str) {
            assert!(matches!(
                cpp(src).next_non_whitespace().unwrap().unwrap().data,
                Token::Literal(LiteralToken::Str(_))
            ));
        }

        assert_same_datetime(
            "__DATE__|__TIME__",
            "\"Jan  1 1970\"|\"00:00:00\"",
            OffsetDateTime::unix_epoch(),
        );
        assert_same_datetime(
            "__DATE__|__TIME__",
            "\"Aug 16 2020\"|\"14:58:36\"",
            OffsetDateTime::from_unix_timestamp(1_597_589_916),
        );

        // Assert current date and time work (without checking value)
        assert_is_str("__DATE__");
        assert_is_str("__TIME__");
    }
}
