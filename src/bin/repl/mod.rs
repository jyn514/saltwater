//! Repl implementation using [`rustyline`].
//!
//! [`rustyline`]: https://docs.rs/rustyline

use commands::default_commands;
use dirs_next::home_dir;
use helper::ReplHelper;
use rustyline::{error::ReadlineError, Cmd, CompletionType, Config, EditMode, Editor, KeyPress};
use std::{collections::HashMap, path::PathBuf};

mod commands;
mod helper;

/// The prefix for commands inside the repl.
const PREFIX: char = ':';
const VERSION: &str = env!("CARGO_PKG_VERSION");
const PROMPT: &str = ">> ";

pub struct Repl {
    editor: Editor<ReplHelper>,
    commands: HashMap<&'static str, fn(&mut Repl, &str)>,
}

impl Repl {
    pub fn new() -> Self {
        let config = Config::builder()
            .history_ignore_space(true)
            .history_ignore_dups(false)
            .completion_type(CompletionType::List)
            .edit_mode(EditMode::Emacs)
            .max_history_size(1000)
            .tab_stop(4)
            .build();
        let mut editor = Editor::with_config(config);

        let commands = default_commands();
        let helper = ReplHelper::new(commands.keys().map(|x| *x).collect());
        editor.set_helper(Some(helper));

        editor.bind_sequence(KeyPress::Up, Cmd::LineUpOrPreviousHistory(1));
        editor.bind_sequence(KeyPress::Down, Cmd::LineDownOrNextHistory(1));
        editor.bind_sequence(KeyPress::Tab, Cmd::Complete);

        Self { editor, commands }
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

    fn save_history(&self) -> Option<()> {
        let path = Self::history_path()?;
        self.editor.save_history(&path).ok()
    }

    fn load_history(&mut self) -> Option<()> {
        let path = Self::history_path()?;
        self.editor.load_history(&path).ok()
    }

    fn history_path() -> Option<PathBuf> {
        let mut history = home_dir()?;
        history.push(".saltwater_history");
        Some(history)
    }

    fn process_line(&mut self, line: String) {
        self.editor.add_history_entry(line.clone());

        if line.trim().starts_with(PREFIX) {
            let name = line.split(' ').next().unwrap();

            match self.commands.get(&name[1..]) {
                Some(action) => action(self, &line[name.len()..]),
                None => println!("unknown command '{}'", name),
            }
        } else {
            todo!()
        }
    }
}
