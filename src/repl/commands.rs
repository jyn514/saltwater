use saltwater::{analyze, Parser, PureAnalyzer};
use std::fmt;

const HELP_MESSAGE: &'static str = "
:help   Shows this message
:type   Shows the type of the given expression
";

#[derive(Debug)]
pub(super) enum CommandError {
    CompileError(saltwater::CompileError),
    UnknownCommand,
}

impl fmt::Display for CommandError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            CommandError::CompileError(err) => writeln!(f, "{}", err.data),
            CommandError::UnknownCommand => writeln!(f, "unknown command"),
        }
    }
}

pub(super) fn run_command(name: &str) -> Result<(), CommandError> {
    match name {
        // TODO: vars: Show variables in scope
        c if c.starts_with("help") => {
            println!("{}", HELP_MESSAGE);
            Ok(())
        }
        c if c.starts_with("type") => show_type(name.trim_start_matches("type")),
        _ => return Err(CommandError::UnknownCommand),
    }
}

fn show_type(code: &str) -> Result<(), CommandError> {
    let ast = analyze(code, Parser::expr, PureAnalyzer::expr)
        .map_err(|e| CommandError::CompileError(e))?;
    println!("Type: {}", ast.ctype);
    Ok(())
}
