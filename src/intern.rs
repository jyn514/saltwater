use std::fmt;
use std::sync::RwLock;

use string_interner::{StringInterner, Sym};

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub struct InternedStr(pub Sym);

impl fmt::Display for InternedStr {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(
            f,
            "{}",
            STRINGS
                .read()
                .expect("failed to lock String cache for reading")
                .resolve(self.0)
                .expect("tried to get value of non-interned string")
        )
    }
}

lazy_static! {
    pub static ref STRINGS: RwLock<StringInterner<Sym>> = RwLock::new(StringInterner::default());
}

pub fn get_or_intern<T: AsRef<str> + Into<String>>(val: T) -> InternedStr {
    InternedStr(
        STRINGS
            .write()
            .expect("failed to lock String cache for writing, another thread must have panicked")
            .get_or_intern(val),
    )
}

pub fn resolve_and_clone(val: InternedStr) -> String {
    let lock = STRINGS
        .read()
        .expect("failed to lock String cache for reading, another thread must have panicked");
    lock.resolve(val.0)
        .expect("tried to get value of non-interned string")
        .to_string()
}
