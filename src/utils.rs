use crate::data::Location;
use ansi_term::{ANSIString, Colour};

fn pretty_print(prefix: ANSIString, msg: &str, location: &Location) {
    eprintln!(
        "{}:{}:{}: {}: {}",
        location.file, location.line, location.column, prefix, msg
    );
}

pub fn warn(msg: &str, location: &Location) {
    pretty_print(Colour::Yellow.bold().paint("warning"), msg, location);
}
pub fn error(msg: &str, location: &Location) {
    pretty_print(Colour::Red.bold().paint("error"), msg, location);
}

/// A simple macro to create a HashMap with minimal fuss.
///
/// Example:
///
/// ```
/// let letters = map!{"a" => "b", "c" => "d"};
/// ```
///
/// Trailing commas are allowed.
macro_rules! map {
    ($( $key: expr => $val: expr ),* $(,)*) => {{
         let mut map = ::std::collections::HashMap::new();
         $( map.insert($key, $val); )*
         map
    }}
}
