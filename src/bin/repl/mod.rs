mod commands;
mod helper;

use commands::CommandError;
use helper::{CommandHinter, ReplHelper};
use rustyline::{
    error::ReadlineError, highlight::MatchingBracketHighlighter,
    validate::MatchingBracketValidator, CompletionType, Config, EditMode, Editor,
};
use saltwater::{
    analyze,
    data::{self, hir, types},
    initialize_jit_module, ir, Opt, Parser, PureAnalyzer, JIT,
};

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
        let module = initialize_jit_module();
        let expr = match analyze(code, Parser::expr, PureAnalyzer::expr) {
            Ok(mut expr) => {
                expr.ctype = types::Type::Int(true);
                expr
            }
            Err(err) => {
                println!("error: {}", err.data);
                return;
            }
        };
        let function_type = types::FunctionType {
            return_type: Box::new(types::Type::Int(true)),
            params: vec![],
            varargs: false,
        };
        let qualifiers = hir::Qualifiers {
            volatile: false,
            c_const: false,
            func: hir::FunctionQualifiers {
                inline: false,
                no_return: false,
            },
        };

        let main = hir::Variable {
            ctype: types::Type::Function(function_type),
            storage_class: data::StorageClass::Extern,
            qualifiers,
            id: saltwater::InternedStr::get_or_intern("main"),
        };

        let span = expr.location;
        let stmt = span.with(hir::StmtType::Return(Some(expr)));
        let init = hir::Initializer::FunctionBody(vec![stmt]);
        let decl = hir::Declaration {
            symbol: main.insert(),
            init: Some(init),
        };
        let (result, _warns) = ir::compile(module, vec![span.with(decl)], false);

        if let Err(err) = result {
            println!("failed to compile: {}", err.data);
            return;
        }

        let module = result.unwrap();
        let mut jit = JIT::from(module);

        let result = unsafe { jit.run_main() }.unwrap();
        println!("result: {}", result);
    }
}
