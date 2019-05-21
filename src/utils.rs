use ansi_term::{ANSIString, Colour};
use crate::data::Location;

fn pretty_print(prefix: ANSIString, msg: &str, location: &Location) {
    eprintln!("{}:{}:{}: {}: {}",
              location.file, location.line,
              location.column, prefix, msg);
}

pub fn warn(msg: &str, location: &Location) {
    pretty_print(Colour::Yellow.bold().paint("warning"), msg, location);
}
pub fn error(msg: &str, location: &Location) {
    pretty_print(Colour::Red.bold().paint("error"), msg, location);
}
