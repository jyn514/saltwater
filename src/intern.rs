use std::fmt;
use std::sync::RwLock;

use lasso::{Rodeo, Spur};
use lazy_static::lazy_static;

use serde::{Deserialize, Serialize};

/// A opaque identifier for a string which has been [interned].
///
/// Interning strings means they are cheap to copy and compare,
/// at the cost of taking an O(n) hash comparison to intern.
/// Interning also reduces memory usage for programs
/// with many identifiers which are repeated often (i.e. C headers).
///
/// [interned]: https://en.wikipedia.org/wiki/String_interning
// TODO: lol this serialize is so wrong
#[derive(Copy, Clone, PartialEq, Eq, Hash, Serialize)]
pub struct InternedStr(pub Spur);

impl fmt::Debug for InternedStr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self)
    }
}

lazy_static! {
    pub static ref STRINGS: RwLock<Rodeo<Spur>> = RwLock::new(Rodeo::default());
    static ref EMPTY_STRING: InternedStr = InternedStr::get_or_intern("");
}

/// Return a `&str` corresponding to this identifier.
///
/// This `&str` can only be used in expression position;
/// attempting to assign it to a variable will give a lifetime error.
/// If you need it to live longer than a single expression, see instead
/// [`InternedStr::resolve_and_clone`] or [`intern::STRINGS`].
///
/// # Panics
/// This function will panic if another thread panicked while accessing the global string pool.
///
/// [`InternedStr::resolve_and_clone`]: intern/struct.InternedStr.html#method.resolve_and_clone
/// [`intern::STRINGS`]: intern/struct.STRINGS.html
#[macro_export]
macro_rules! get_str {
    ($self: expr) => {{
        let tmp = $self.0;
        $crate::intern::STRINGS
            .read()
            .expect("failed to lock String cache for reading")
            .resolve(&tmp)
    }};
}

impl InternedStr {
    /// Return whether `self` is the empty string.
    pub fn is_empty(self) -> bool {
        self == *EMPTY_STRING
    }
    /// Convert this identifier back into the original `String`, cloning it along the way.
    ///
    /// # See also
    /// [`get_str!`](../macro.get_str.html)
    ///
    /// # Panics
    /// This function will panic if another thread panicked while accessing the global string pool.
    ///
    pub fn resolve_and_clone(self) -> String {
        get_str!(self).to_string()
    }
    /// Intern this string into the string pool and return an opaque identifier.
    ///
    /// If `val` is already present, it will not be duplicated (i.e. this method is idempotent).
    ///
    /// # Panics
    /// This function will panic if another thread panicked while accessing the global string pool.
    ///
    pub fn get_or_intern<T: AsRef<str> + Into<String>>(val: T) -> InternedStr {
        InternedStr(
            STRINGS
                .write()
                .expect(
                    "failed to lock String cache for writing, another thread must have panicked",
                )
                .get_or_intern(val),
        )
    }
}

impl fmt::Display for InternedStr {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", get_str!(self))
    }
}

impl Default for InternedStr {
    fn default() -> Self {
        *EMPTY_STRING
    }
}

impl From<&str> for InternedStr {
    fn from(s: &str) -> Self {
        Self::get_or_intern(s)
    }
}

impl From<String> for InternedStr {
    fn from(s: String) -> Self {
        Self::get_or_intern(s)
    }
}

#[cfg(test)]
mod proptest_impl {
    use super::InternedStr;
    use proptest::prelude::*;
    impl Arbitrary for InternedStr {
        type Parameters = String;
        type Strategy = Just<InternedStr>;

        fn arbitrary_with(s: Self::Parameters) -> Self::Strategy {
            Just(s.into())
        }
    }
}
