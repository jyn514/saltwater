mod commands;
mod helper;

use commands::CommandError;
use cranelift_module::Module;
use cranelift_simplejit::SimpleJITBackend;
use helper::{CommandHinter, ReplHelper};
use rustyline::{
    error::ReadlineError, highlight::MatchingBracketHighlighter,
    validate::MatchingBracketValidator, CompletionType, Config, EditMode, Editor,
};
use saltwater::{analyze, check_semantics, initialize_jit_module, Opt, Parser, PureAnalyzer};

const PROMPT: &str = ">> ";
const COMMAND_PREFIX: &str = ":";

const COMMANDS: [(&'static str, fn(String) -> Result<(), CommandError>); 4] = [
    ("help", commands::print_help),
    ("quit", commands::quit_repl),
    ("q", commands::quit_repl),
    ("type", commands::show_type),
];

#[allow(unused)]
pub struct Repl<'s> {
    editor: Editor<ReplHelper>,
    prefix: &'s str,
    prompt: &'s str,
    opt: Opt,
    code: String,
    module: Module<SimpleJITBackend>,
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
            hinter: CommandHinter,
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
            module: initialize_jit_module(),
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
        let cmd = COMMANDS.iter().filter(|(k, _v)| args.starts_with(k)).next();
        let result = if let Some((name, cmd)) = cmd {
            let args = &args[name.len()..];
            cmd(args.to_string())
        } else {
            commands::print_help(args.to_string())
        };

        match result {
            Ok(_) => {}
            Err(err) => println!("{}", err),
        }
    }

    fn execute_code(&mut self, code: &str) {
        let program = check_semantics(code, self.opt.clone());
    }
}
