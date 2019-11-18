use std::process;
use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::RwLock;

use ansi_term::{ANSIString, Colour};
use string_interner::{StringInterner, Sym};

use crate::data::Location;

pub type InternType = Sym;

static WARNINGS: AtomicUsize = AtomicUsize::new(0);
static ERRORS: AtomicUsize = AtomicUsize::new(0);
lazy_static! {
    pub static ref STRINGS: RwLock<StringInterner<InternType>> =
        RwLock::new(StringInterner::default());
}

pub fn get_or_intern<T: AsRef<str> + Into<String>>(val: T) -> InternType {
    STRINGS
        .write()
        .expect("failed to lock String cache for writing, another thread must have panicked")
        .get_or_intern(val)
}

pub fn resolve_and_clone<'a>(val: InternType) -> String {
    let lock = STRINGS
        .read()
        .expect("failed to lock String cache for reading, another thread must have panicked");
    lock.resolve(val)
        .expect("tried to get value of non-interned string")
        .to_string()
}

fn pretty_print(prefix: ANSIString, msg: &str, location: &Location) {
    println!(
        "{}:{}:{}: {}: {}",
        STRINGS.read().unwrap().resolve(location.file).unwrap(),
        location.line,
        location.column,
        prefix,
        msg
    );
}

pub fn warn(msg: &str, location: &Location) {
    WARNINGS.fetch_add(1, Ordering::Relaxed);
    pretty_print(Colour::Yellow.bold().paint("warning"), msg, location);
}
pub fn error(msg: &str, location: &Location) {
    ERRORS.fetch_add(1, Ordering::Relaxed);
    pretty_print(Colour::Red.bold().paint("error"), msg, location);
}
pub fn fatal<T: std::fmt::Display>(msg: T, code: i32) -> ! {
    eprintln!("{}: {}", Colour::Black.bold().paint("fatal"), msg);
    process::exit(code);
}

pub fn get_warnings() -> usize {
    WARNINGS.load(Ordering::SeqCst)
}

pub fn get_errors() -> usize {
    ERRORS.load(Ordering::SeqCst)
}

/// ensure that a condition is true at compile time
/// thanks to https://nikolaivazquez.com/posts/programming/rust-static-assertions/
macro_rules! const_assert {
    ($condition:expr) => {
        #[deny(const_err)]
        #[allow(dead_code)]
        const ASSERT: usize = 0 - !$condition as usize;
    };
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

/// Check if an expression matches a pattern.
///
/// Very similar to `if let $pattern = $expr {}`,
/// but can be used as an expression instead of a block.
#[allow(unused_macros)]
macro_rules! matches {
    ($pattern: pat, $val: expr) => {
        match $val {
            $pattern => true,
            _ => false,
        }
    };
}

/// Return an error from a function
/// Assumes that 'Locatable' is in scope and that the function it is called in
/// returns a 'Result<Locatable<T>>'
macro_rules! err {
    ($message: expr, $location: expr$(,)?) => {
        return Err(Locatable {
            data: $message,
            location: $location,
        });
    };
}

/// Check that many expressions match a pattern
/// TODO: only works for 1, 2, or 3 arguments
#[allow(unused_macros)]
macro_rules! all_match {
    ($pat: pat, $val: expr) => {
        matches!($pat, $val)
    };
    ($pat: pat, $val: expr, $val2: expr) => {
        matches!($pat, $val) && matches!($pat, $val2)
    };
    ($pat: pat, $val: expr, $val2: expr, $val3: expr) => {
        matches!($pat, $val) && matches!($pat, $val2) && matches!($pat, $val3)
    };
    ($pat: pat, $val: expr, $val2: expr, $val3: expr, $val4: expr) => {
        matches!($pat, $val)
            && matches!($pat, $val2)
            && matches!($pat, $val3)
            && matches!($pat, $val4)
    };
}
