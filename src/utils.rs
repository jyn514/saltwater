use std::sync::atomic::{AtomicUsize, Ordering};

use ansi_term::{ANSIString, Colour};

use crate::data::Location;

static WARNINGS: AtomicUsize = AtomicUsize::new(0);
static ERRORS: AtomicUsize = AtomicUsize::new(0);

fn pretty_print(prefix: ANSIString, msg: &str, location: &Location) {
    eprintln!(
        "{}:{}:{}: {}: {}",
        location.file, location.line, location.column, prefix, msg
    );
}

pub(crate) fn warn(msg: &str, location: &Location) {
    WARNINGS.fetch_add(1, Ordering::Relaxed);
    pretty_print(Colour::Yellow.bold().paint("warning"), msg, location);
}
pub(crate) fn error(msg: &str, location: &Location) {
    ERRORS.fetch_add(1, Ordering::Relaxed);
    pretty_print(Colour::Red.bold().paint("error"), msg, location);
}

pub(crate) fn get_warnings() -> usize {
    WARNINGS.load(Ordering::SeqCst)
}

pub(crate) fn get_errors() -> usize {
    ERRORS.load(Ordering::SeqCst)
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
