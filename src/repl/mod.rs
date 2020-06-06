mod commands;
mod helper;

use crate::Opt;
use helper::ReplHelper;
use rustyline::{
    error::ReadlineError, highlight::MatchingBracketHighlighter,
    validate::MatchingBracketValidator, CompletionType, Config, EditMode, Editor,
};
use std::collections::HashMap;

const PROMPT: &str = ">> ";
const COMMAND_PREFIX: &str = ":";

#[allow(unused)]
pub struct Repl<'s> {
    editor: Editor<ReplHelper>,
    prefix: &'s str,
    prompt: &'s str,
    opt: Opt,
    code: String,
}

impl<'s> Repl<'s> {
    pub fn new(opt: Opt) -> Self {
        let config = Config::builder()
            .history_ignore_space(true)
            .completion_type(CompletionType::List)
            .edit_mode(EditMode::Emacs)
            .build();
        let helper = ReplHelper {
            highlighter: MatchingBracketHighlighter::new(),
            validator: MatchingBracketValidator::new(),
        };
        let mut editor = Editor::with_config(config);
        editor.set_helper(Some(helper));
        // TODO: Set some more key binds here. Definitely hist up / down
        // and add Vim Mode support.
        Self {
            editor,
            opt,
            prefix: COMMAND_PREFIX,
            prompt: PROMPT,
            code: String::new(),
        }
    }

    pub fn run(&mut self) -> rustyline::Result<()> {
        loop {
            let line = self.editor.readline(self.prompt);
            match line {
                Ok(line) => self.process_line(line),
                // Ctrl + C will skip the abort the current line
                // and asks for new input
                Err(ReadlineError::Interrupted) => continue,
                // Ctrl + D will exit the repl
                Err(ReadlineError::Eof) => return Ok(()),
                Err(err) => return Err(err),
            }
        }
    }

    fn process_line(&mut self, line: String) {
        if line.starts_with(self.prefix) {
            self.run_command(&line[self.prefix.len()..])
        } else {
            self.execute_code(line.as_str())
        }
    }

    fn run_command(&mut self, args: &str) {
        let result = match args {
            s if s.starts_with("expr") => todo!(),
            s if s.starts_with("decl") => todo!(),
            s if s.starts_with("stmt") => todo!(),
            _ => commands::run_command(args),
        };

        match result {
            Ok(_) => {}
            Err(err) => println!("{}", err),
        }
    }

    fn execute_code(&mut self, _code: &str) {
        todo!();
    }
}
