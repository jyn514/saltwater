use crate::{
    commands::default_commands, commands::generate_help_message, commands::Command,
    helper::ReplHelper,
};
use dirs_next::data_dir;
use rustyline::{error::ReadlineError, Cmd, CompletionType, Config, EditMode, Editor, KeyPress};
use saltwater_codegen::{initialize_jit_module, JIT};
use saltwater_parser::{
    data, hir, hir::Declaration, hir::Expr, types, CompileError, Locatable, Parser,
    PreProcessorBuilder, PureAnalyzer, Type,
};
use std::path::PathBuf;

/// The prefix for commands inside the repl.
pub(crate) const PREFIX: char = ':';
const VERSION: &str = env!("CARGO_PKG_VERSION");
const PROMPT: &str = ">> ";

macro_rules! execute {
    ($fun:ident, $ty:path, $action:expr) => {
        $action(unsafe {
            let execute: unsafe extern "C" fn() -> $ty = std::mem::transmute($fun);
            execute()
        });
    };
}

pub struct Repl {
    editor: Editor<ReplHelper>,
    commands: Vec<Command>,
    /// Generated help message for all commands.
    pub help_message: String,
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
        let help_message = generate_help_message(&commands);
        let helper = ReplHelper::new(commands.iter().flat_map(|cmd| cmd.names).copied().collect());
        editor.set_helper(Some(helper));

        editor.bind_sequence(KeyPress::Up, Cmd::LineUpOrPreviousHistory(1));
        editor.bind_sequence(KeyPress::Down, Cmd::LineDownOrNextHistory(1));
        editor.bind_sequence(KeyPress::Tab, Cmd::Complete);

        Self {
            editor,
            commands,
            help_message,
        }
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

    pub fn save_history(&self) -> Option<()> {
        let path = Self::history_path()?;
        self.editor.save_history(&path).ok()
    }

    fn load_history(&mut self) -> Option<()> {
        let path = Self::history_path()?;
        self.editor.load_history(&path).ok()
    }

    fn history_path() -> Option<PathBuf> {
        let mut history = data_dir()?;
        history.push("saltwater_history");
        Some(history)
    }

    fn process_line(&mut self, line: String) {
        self.editor.add_history_entry(line.clone());

        let line = line.trim();
        if line.starts_with(PREFIX) {
            let name = line.split(' ').next().unwrap();

            match self
                .commands
                .iter()
                .find(|cmd| cmd.names.contains(&&name[1..]))
            {
                Some(cmd) => {
                    let action = cmd.action;
                    action(self, &line[name.len()..])
                }
                None => println!("unknown command '{}'", name),
            }
        } else {
            match self.execute_code(line) {
                Ok(_) => {}
                Err(err) => {
                    // TODO: Proper error reporting
                    println!("error: {}", err.data);
                }
            }
        }
    }

    fn execute_code(&mut self, code: &str) -> Result<(), CompileError> {
        let module = initialize_jit_module();

        let expr = analyze_expr(code)?;
        let expr_ty = expr.ctype.clone();
        let _decl = wrap_expr(expr);

        let mut jit = JIT::from(module);
        jit.finalize();
        let fun = jit
            .get_compiled_function("execute")
            .expect("this is not good.");

        match expr_ty {
            Type::Short(signed) => execute!(fun, i16, |x| match signed {
                true => println!("=> {}", x),
                false => println!("=> {}", x as u16),
            }),
            Type::Int(signed) => execute!(fun, i32, |x| match signed {
                true => println!("=> {}", x),
                false => println!("=> {}", x as u32),
            }),
            Type::Long(signed) => execute!(fun, i64, |x| match signed {
                true => println!("=> {}", x),
                false => println!("=> {}", x as u64),
            }),
            Type::Float => execute!(fun, f32, |f| println!("=> {}", f)),
            Type::Double => execute!(fun, f64, |f| println!("=> {}", f)),

            Type::Char(_) => execute!(fun, char, |c| println!("=> {}", c)),
            Type::Bool => execute!(fun, bool, |b| println!("=> {}", b)),
            Type::Void => unsafe {
                let execute: unsafe extern "C" fn() = std::mem::transmute(fun);
                execute()
            },

            // TODO: Implement execution for more types
            ty => println!("error: expression returns unsupported type: {:?}", ty),
        };
        Ok(())
    }
}

/// Takes an expression and wraps it into a `execute` function that looks like the following:
///
/// ```
/// <type> execute() {
///     return <expr>;
/// }
/// ```
fn wrap_expr(expr: Expr) -> Locatable<Declaration> {
    let fun = hir::Variable {
        ctype: types::Type::Function(types::FunctionType {
            return_type: Box::new(expr.ctype.clone()),
            params: vec![],
            varargs: false,
        }),
        storage_class: data::StorageClass::Extern,
        qualifiers: Default::default(),
        id: "execute".into(),
    };

    let span = expr.location;
    let return_stmt = span.with(hir::StmtType::Return(Some(expr)));
    let init = hir::Initializer::FunctionBody(vec![return_stmt]);
    let decl = hir::Declaration {
        symbol: fun.insert(),
        init: Some(init),
    };
    span.with(decl)
}

pub fn analyze_expr(code: &str) -> Result<Expr, Locatable<data::Error>> {
    let code = format!("{}\n", code).into_boxed_str();
    let cpp = PreProcessorBuilder::new(code).build();
    let mut parser = Parser::new(cpp, false);
    let expr = parser.expr()?;

    let mut analyzer = PureAnalyzer::new();
    let expr = analyzer.expr(expr);

    if let Some(err) = analyzer.errors().pop_front() {
        return Err(err);
    }

    Ok(expr)
}
