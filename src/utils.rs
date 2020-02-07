use core::cell::RefCell;
use std::process;

use ansi_term::Colour;

pub fn fatal<T: std::fmt::Display>(msg: T, code: i32) -> ! {
    eprintln!("{}: {}", Colour::Black.bold().paint("fatal"), msg);
    process::exit(code);
}

// this is just a guesstimate, it should probably be configurable
#[cfg(debug_assertions)]
const MAX_DEPTH: usize = 50;
#[cfg(not(debug_assertions))]
const MAX_DEPTH: usize = 200;

thread_local!(static RECURSION_DEPTH: RefCell<usize> = RefCell::new(0));

// make sure we don't crash on highly nested expressions
// or rather, crash in a controlled way
pub(crate) fn recursion_check() {
    RECURSION_DEPTH.with(|depth| {
        let d = *depth.borrow();
        if d > MAX_DEPTH {
            eprintln!(
                "fatal: maximum recursion depth exceeded ({} > {})",
                d, MAX_DEPTH
            );
            std::process::exit(102);
        } else {
            *depth.borrow_mut() = d + 1;
        }
    })
}

pub(crate) fn recursion_done() {
    RECURSION_DEPTH.with(|depth| {
        let d = *depth.borrow();
        *depth.borrow_mut() = d - 1;
    });
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

/// Return an error from a function
/// Assumes that 'Locatable' is in scope and that the function it is called in
/// returns a 'Result<Locatable<T>>'
macro_rules! semantic_err {
    ($message: expr, $location: expr $(,)?) => {
        return Err(CompileError::semantic(Locatable {
            data: $message,
            location: $location,
        }));
    };
}
