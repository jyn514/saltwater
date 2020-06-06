use super::COMMANDS;
use rustyline::{
    completion::{Completer, Pair},
    error::ReadlineError,
    highlight::{Highlighter, MatchingBracketHighlighter},
    hint::Hinter,
    validate::{self, MatchingBracketValidator, Validator},
    Context,
};
use rustyline_derive::Helper;
use std::borrow::Cow;

#[derive(Helper)]
pub(super) struct ReplHelper {
    pub(super) highlighter: MatchingBracketHighlighter,
    pub(super) validator: MatchingBracketValidator,
    pub(super) hinter: CommandHinter,
}

impl Completer for ReplHelper {
    type Candidate = Pair;

    fn complete(
        &self,
        _line: &str,
        _pos: usize,
        _ctx: &Context<'_>,
    ) -> Result<(usize, Vec<Pair>), ReadlineError> {
        Ok((0, vec![]))
    }
}

impl Hinter for ReplHelper {
    fn hint(&self, line: &str, pos: usize, ctx: &Context<'_>) -> Option<String> {
        self.hinter.hint(line, pos, ctx)
    }
}

impl Highlighter for ReplHelper {
    fn highlight_prompt<'b, 's: 'b, 'p: 'b>(
        &'s self,
        prompt: &'p str,
        _default: bool,
    ) -> Cow<'b, str> {
        Cow::Borrowed(prompt)
    }

    fn highlight_hint<'h>(&self, hint: &'h str) -> Cow<'h, str> {
        let style = ansi_term::Style::new().dimmed();
        Cow::Owned(style.paint(hint).to_string())
    }

    fn highlight<'l>(&self, line: &'l str, pos: usize) -> Cow<'l, str> {
        self.highlighter.highlight(line, pos)
    }

    fn highlight_char(&self, line: &str, pos: usize) -> bool {
        self.highlighter.highlight_char(line, pos)
    }
}

impl Validator for ReplHelper {
    fn validate(
        &self,
        ctx: &mut validate::ValidationContext,
    ) -> rustyline::Result<validate::ValidationResult> {
        self.validator.validate(ctx)
    }

    fn validate_while_typing(&self) -> bool {
        self.validator.validate_while_typing()
    }
}

pub(super) struct CommandHinter;

impl Hinter for CommandHinter {
    fn hint(&self, line: &str, pos: usize, _ctx: &Context<'_>) -> Option<String> {
        if pos < line.len() {
            return None;
        }
        let start = &line[..pos];
        if !start.starts_with(":") {
            return None;
        }

        COMMANDS
            .iter()
            .filter(|(k, _v)| k.starts_with(&start[1..]))
            .map(|(k, _v)| k)
            .next()
            .map(|s| s.to_string())
    }
}
