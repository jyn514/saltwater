use crate::repl::PREFIX;
use owo_colors::OwoColorize;
use rustyline::{
    completion::{extract_word, Candidate, Completer},
    highlight::{Highlighter, MatchingBracketHighlighter},
    hint::Hinter,
    validate::{ValidationContext, ValidationResult, Validator},
    Context,
};
use rustyline_derive::Helper;
use std::borrow::Cow;

#[derive(Helper)]
pub struct ReplHelper {
    highlighter: MatchingBracketHighlighter,
    commands: Vec<&'static str>,
}

impl ReplHelper {
    pub fn new(commands: Vec<&'static str>) -> Self {
        Self {
            commands,
            highlighter: Default::default(),
        }
    }
}

impl Highlighter for ReplHelper {
    fn highlight<'l>(&self, line: &'l str, pos: usize) -> Cow<'l, str> {
        // TODO: Syntax highlighting.
        self.highlighter.highlight(line, pos)
    }

    fn highlight_hint<'h>(&self, hint: &'h str) -> Cow<'h, str> {
        Cow::Owned(hint.dimmed().to_string())
    }

    fn highlight_char(&self, line: &str, pos: usize) -> bool {
        self.highlighter.highlight_char(line, pos)
    }
}

impl Validator for ReplHelper {
    fn validate(&self, ctx: &mut ValidationContext<'_>) -> rustyline::Result<ValidationResult> {
        if ctx.input().starts_with(crate::repl::PREFIX) {
            if self.commands.contains(&&ctx.input()[1..]) {
                return Ok(ValidationResult::Valid(None));
            } else {
                return Ok(ValidationResult::Invalid(None));
            }
        }

        let result = crate::repl::analyze_expr(ctx.input().to_string());
        if let Err(err) = result {
            Ok(ValidationResult::Invalid(Some(err.data.to_string())))
        } else {
            Ok(ValidationResult::Valid(None))
        }
    }
}

impl Hinter for ReplHelper {
    fn hint(&self, line: &str, pos: usize, _ctx: &Context<'_>) -> Option<String> {
        let start = &line[..pos];
        if !start.starts_with(PREFIX) {
            return None;
        }
        let start = &start[PREFIX.len_utf8()..];
        self.commands
            .iter()
            .find(|cmd| cmd.starts_with(start))
            .map(|hint| String::from(&hint[start.len()..]))
    }
}

/// Wrapper around a `&'static str` to be used for completion candidates.
pub struct CompletionCandidate {
    display: &'static str,
}

impl Candidate for CompletionCandidate {
    fn display(&self) -> &str {
        self.display
    }

    fn replacement(&self) -> &str {
        self.display
    }
}

impl Completer for ReplHelper {
    type Candidate = CompletionCandidate;

    fn complete(
        &self,
        line: &str,
        pos: usize,
        _ctx: &Context<'_>,
    ) -> rustyline::Result<(usize, Vec<Self::Candidate>)> {
        let (idx, word) = extract_word(line, pos, None, &[]);
        if !line.starts_with(PREFIX) {
            return Ok((0, vec![]));
        }
        let word = word.trim_matches(PREFIX);

        let commands = self
            .commands
            .iter()
            .filter(|cmd| cmd.starts_with(word))
            .map(|x| CompletionCandidate { display: x })
            .collect::<Vec<_>>();

        Ok((idx + 1, commands))
    }

    // TODO: Complete method names, types, etc.
}
