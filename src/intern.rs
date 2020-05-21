use std::fmt;
use std::sync::RwLock;

use lasso::{Rodeo, Spur};
use lazy_static::lazy_static;

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub struct InternedStr(pub Spur);

lazy_static! {
    pub static ref STRINGS: RwLock<Rodeo<Spur>> = RwLock::new(Rodeo::default());
    static ref EMPTY_STRING: InternedStr = InternedStr::get_or_intern("");
}

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
    pub fn is_empty(self) -> bool {
        self == *EMPTY_STRING
    }
    pub fn resolve_and_clone(self) -> String {
        get_str!(self).to_string()
    }
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
