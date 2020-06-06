use saltwater::{analyze, Parser, PureAnalyzer};
use std::fmt;

const HELP_MESSAGE: &'static str = "
:help   Shows this message
:type   Shows the type of the given expression
";

#[derive(Debug)]
pub(super) enum CommandError {
    CompileError(saltwater::CompileError),
}

impl fmt::Display for CommandError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            CommandError::CompileError(err) => writeln!(f, "{}", err.data),
        }
    }
}

pub(super) fn show_type(code: String) -> Result<(), CommandError> {
    let ast = analyze(&code, Parser::expr, PureAnalyzer::expr)
        .map_err(|e| CommandError::CompileError(e))?;
    println!("Type: {}", ast.ctype);
    Ok(())
}

pub(super) fn print_help(_code: String) -> Result<(), CommandError> {
    println!("{}", HELP_MESSAGE);
    Ok(())
}
