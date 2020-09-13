use crate::{
    commands::default_commands, commands::generate_help_message, commands::Command,
    helper::ReplHelper,
};
use dirs_next::data_dir;
use rustyline::{error::ReadlineError, Cmd, CompletionType, Config, EditMode, Editor, KeyPress};
use saltwater_codegen::{compile_decl, initialize_jit_module, JIT};
use saltwater_parser::{
    data, hir, hir::Declaration, hir::Expr, types, CompileError, Locatable, Parser,
    PreProcessorBuilder, PureAnalyzer, Type,
};
use std::path::PathBuf;

#[cfg(not(target_pointer_width = "64"))]
compile_error!("only x86_64 is supported");

/// The prefix for commands inside the repl.
pub(crate) const PREFIX: char = ':';
const VERSION: &str = env!("CARGO_PKG_VERSION");
const PROMPT: &str = ">> ";

/// Takes a function pointer and transmute it into a function
/// that returns the given type. Then executes it and returns the result.
///
/// # Safety
///
/// `$fun` has to be a valid pointer to a function that returns the `$ty`.
macro_rules! execute {
    ($fun:ident, $ty:tt) => {
        unsafe {
            let execute = std::mem::transmute::<*const u8, unsafe extern "C" fn() -> $ty>($fun);
            execute()
        }
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
        println!("Type {}help for more information.", PREFIX);
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

        let trimmed_line = line.trim();
        if trimmed_line.starts_with(PREFIX) {
            let name = trimmed_line.split(' ').next().unwrap();

            match self
                .commands
                .iter()
                .find(|cmd| cmd.names.contains(&&name[1..]))
            {
                Some(cmd) => {
                    let action = cmd.action;
                    action(self, &trimmed_line[name.len()..])
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

    fn execute_code(&mut self, code: String) -> Result<(), CompileError> {
        let module = initialize_jit_module();

        let expr = analyze_expr(code)?;
        let expr_ty = expr.ctype.clone();
        let decl = wrap_expr(expr);
        let module = compile_decl(module, decl, Default::default())?;

        let mut jit = JIT::from(module);
        jit.finalize();
        let fun = jit
            .get_compiled_function("execute")
            .expect("wrap_expr should create a function named `execute`");

        match expr_ty {
            Type::Short(true) => println!("=> {}", execute!(fun, i16)),
            Type::Short(false) => println!("=> {}", execute!(fun, u16)),

            Type::Int(true) => println!("=> {}", execute!(fun, i32)),
            Type::Int(false) => println!("=> {}", execute!(fun, u32)),

            Type::Long(true) => println!("=> {}", execute!(fun, i64)),
            Type::Long(false) => println!("=> {}", execute!(fun, u64)),

            Type::Float => println!("=> {}", execute!(fun, f32)),
            Type::Double => println!("=> {}", execute!(fun, f64)),

            Type::Char(_) => {
                let c = execute!(fun, u8);
                if c.is_ascii() {
                    println!("=> {}", c);
                } else {
                    println!("=> {}", hex::encode(&[c]));
                }
            }
            Type::Bool => println!("=> {}", execute!(fun, bool)),
            Type::Void => execute!(fun, ()),

            // TODO: Implement execution for more types
            ty => println!("error: expression has an unsupported type: {:?}", ty),
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
        storage_class: data::StorageClass::Static,
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

pub fn analyze_expr(mut code: String) -> Result<Expr, Locatable<data::Error>> {
    code.push('\n');
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
