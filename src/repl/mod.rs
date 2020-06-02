mod helper;

use crate::Opt;
use helper::ReplHelper;
use rustyline::{
    error::ReadlineError, highlight::MatchingBracketHighlighter, hint::HistoryHinter,
    validate::MatchingBracketValidator, CompletionType, Config, EditMode, Editor,
};

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
            hinter: HistoryHinter {},
        };
        let mut editor = Editor::with_config(config);
        editor.set_helper(Some(helper));
        // TODO: Set some more key binds here. Definitely hist up / down
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
                // Ctrl + C will do nothing
                Err(ReadlineError::Interrupted) => continue,
                // Ctrl + D will exit the repl
                Err(ReadlineError::Eof) => std::process::exit(0),
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

    fn run_command(&mut self, _args: &str) {
        todo!();
    }

    fn execute_code(&mut self, _code: &str) {
        todo!();
    }
}
