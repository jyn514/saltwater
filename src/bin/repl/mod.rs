//! Repl implementation using [`rustyline`].
//!
//! [`rustyline`]: https://docs.rs/rustyline

use dirs_next::home_dir;
use helper::ReplHelper;
use rustyline::{error::ReadlineError, Cmd, CompletionType, Config, EditMode, Editor, KeyPress};
use std::path::PathBuf;

mod helper;

/// The prefix for commands inside the repl.
const PREFIX: &str = ":";
const VERSION: &str = env!("CARGO_PKG_VERSION");
const PROMPT: &str = ">> ";

#[derive(Debug)]
pub struct Repl {
    editor: Editor<ReplHelper>,
}

impl Repl {
    pub fn new() -> Self {
        let config = Config::builder()
            .history_ignore_space(true)
            .history_ignore_dups(false)
            .completion_type(CompletionType::List)
            .edit_mode(EditMode::Emacs)
            .tab_stop(4)
            .build();
        let mut editor = Editor::with_config(config);

        let helper = ReplHelper::new(vec!["help".to_string()]);
        editor.set_helper(Some(helper));

        editor.bind_sequence(KeyPress::Up, Cmd::LineUpOrPreviousHistory(1));
        editor.bind_sequence(KeyPress::Down, Cmd::LineDownOrNextHistory(1));

        Self { editor }
    }

    pub fn run(&mut self) -> rustyline::Result<()> {
        self.load_history();

        println!("Saltwater {}", VERSION);
        println!(r#"Type "{}help" for more information."#, PREFIX);
        let result = loop {
            let line = self.editor.readline(PROMPT);
            match line {
                Ok(line) => self.process_line(line),
                // Ctrl + c will abort the current line.
                Err(ReadlineError::Interrupted) => continue,
                // Ctrl + d will exit the repl.
                Err(ReadlineError::Eof) => break Ok(()),
                Err(err) => break Err(err),
            }
        };
        self.save_history();

        result
    }

    fn history_path() -> Option<PathBuf> {
        let mut history = home_dir()?;
        history.push(".saltwater_history");
        Some(history)
    }

    fn save_history(&self) -> Option<()> {
        let path = Self::history_path()?;
        self.editor.save_history(&path).ok()
    }

    fn load_history(&mut self) -> Option<()> {
        let path = Self::history_path()?;
        self.editor.load_history(&path).ok()
    }

    fn process_line(&mut self, line: String) {
        self.editor.add_history_entry(line);
    }
}
