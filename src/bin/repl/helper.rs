use ansi_term::Style;
use rustyline::{
    completion::Completer,
    highlight::{Highlighter, MatchingBracketHighlighter},
    hint::Hinter,
    validate::{ValidationContext, ValidationResult, Validator},
};
use rustyline_derive::Helper;
use std::borrow::Cow;

#[derive(Helper)]
pub struct ReplHelper {
    highlighter: MatchingBracketHighlighter,
    commands: Vec<String>,
}

impl ReplHelper {
    pub fn new(commands: Vec<String>) -> Self {
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
        let hint = Style::new().dimmed().paint(hint);
        Cow::Owned(hint.to_string())
    }

    fn highlight_char(&self, line: &str, pos: usize) -> bool {
        self.highlighter.highlight_char(line, pos)
    }
}

impl Validator for ReplHelper {
    fn validate(&self, ctx: &mut ValidationContext) -> rustyline::Result<ValidationResult> {
        let input = ctx.input();
        let mut stack = vec![];

        for c in input.chars() {
            match c {
                '(' | '[' | '{' => stack.push(c),
                ')' | ']' | '}' => match (stack.pop(), c) {
                    (Some('('), ')') | (Some('['), ']') | (Some('{'), '}') => {}
                    (_, _) => {
                        return Ok(ValidationResult::Invalid(Some(
                            "unclosed delimiter".to_string(),
                        )));
                    }
                },
                _ => continue,
            }
        }

        if stack.is_empty() {
            Ok(ValidationResult::Valid(None))
        } else {
            Ok(ValidationResult::Incomplete)
        }
    }
}

impl Hinter for ReplHelper {
    fn hint(&self, line: &str, pos: usize, ctx: &rustyline::Context<'_>) -> Option<String> {
        let start = &line[..pos];
        if !start.starts_with(super::PREFIX) {
            return None;
        }
        let start = &start[1..];
        self.commands
            .iter()
            .find(|cmd| cmd.starts_with(start))
            .map(|hint| String::from(&hint[start.len()..]))
    }
}

impl Completer for ReplHelper {
    type Candidate = String;

    // TODO: Complete method names, types, etc.
}
