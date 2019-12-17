use std::process;
use std::sync::atomic::{AtomicUsize, Ordering};

use ansi_term::{ANSIString, Colour};

use crate::data::lex::Location;
use crate::intern::STRINGS;

static WARNINGS: AtomicUsize = AtomicUsize::new(0);

pub fn pretty_print<T: std::fmt::Display>(prefix: ANSIString, msg: T, location: Location) {
    println!(
        "{}:{}:{}: {}: {}",
        STRINGS.read().unwrap().resolve(location.file.0).unwrap(),
        location.line,
        location.column,
        prefix,
        msg
    );
}

pub fn warn(msg: &str, location: Location) {
    WARNINGS.fetch_add(1, Ordering::Relaxed);
    pretty_print(Colour::Yellow.bold().paint("warning"), msg, location);
}
pub fn fatal<T: std::fmt::Display>(msg: T, code: i32) -> ! {
    eprintln!("{}: {}", Colour::Black.bold().paint("fatal"), msg);
    process::exit(code);
}

pub fn get_warnings() -> usize {
    WARNINGS.load(Ordering::SeqCst)
}

/// (f, g) => f . g
pub fn compose<'a, A, B, C, G, F>(f: F, g: G) -> impl Fn(A) -> C + 'a
where
    F: 'a + Fn(B) -> C,
    G: 'a + Fn(A) -> B,
{
    move |x| f(g(x))
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

/// A simple macro to create a VecDeque from a list of initial elements.
///
/// Very similar to `vec![]` from the standard library.
/// Example:
/// ```rust
/// let queue = vec_deque![1, 2, 3];
/// ```
///
/// Trailing commas are allowed.
macro_rules! vec_deque {
    ($elem:expr; $n:expr) => ({
        use std::collections::VecDeque;
        VecDeque::from(vec![$elem; $n])
    });
    ($($x: expr),*) => ({
        use std::collections::VecDeque;
        VecDeque::from(vec![$($x),*])
    });
    ($($x:expr,)*) => ($crate::vec_deque![$($x),*])
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
macro_rules! semantic_err {
    ($message: expr, $location: expr$(,)?) => {
        return Err(CompileError::Semantic(Locatable {
            data: $message,
            location: $location,
        })
        .into());
    };
}

macro_rules! syntax_err {
    ($message: expr, $location: expr$(,)?) => {
        return Err(Locatable {
            data: $message,
            location: $location,
        }
        .into());
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
