use std::fmt;
use std::sync::RwLock;

use string_interner::{StringInterner, Sym, Symbol};

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub struct InternedStr(pub Sym);

lazy_static! {
    pub static ref STRINGS: RwLock<StringInterner<Sym>> = RwLock::new(StringInterner::default());
    static ref EMPTY_STRING: InternedStr = InternedStr::get_or_intern("");
}

#[macro_export]
macro_rules! get_str {
    ($self: expr) => {
        $crate::intern::STRINGS
            .read()
            .expect("failed to lock String cache for reading")
            .resolve($self.0)
            .expect("tried to get value of non-interned string")
    };
}

impl InternedStr {
    #[inline(always)]
    pub fn to_usize(self) -> usize {
        self.0.to_usize()
    }
    pub fn len(self) -> usize {
        get_str!(self).len()
    }
    pub fn is_empty(self) -> bool {
        self == Default::default()
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
