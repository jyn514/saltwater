#![no_main]
#[macro_use]
extern crate libfuzzer_sys;
extern crate rcc;

fuzz_target!(|data: &[u8]| {
    if let Ok(s) = std::str::from_utf8(data) {
        rcc::compile(s.into(), "<fuzz test>".into(), false, false, false);
    }
});
