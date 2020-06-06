use std::fmt;

#[derive(Debug)]
pub(super) enum CommandError {
    UnknownCommand,
}

impl fmt::Display for CommandError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            CommandError::UnknownCommand => writeln!(f, "unknown command"),
        }
    }
}

pub(super) fn run_command(name: &str) -> Result<(), CommandError> {
    match name {
        _ => return Err(CommandError::UnknownCommand),
    }
}
