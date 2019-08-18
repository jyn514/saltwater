#![no_main]
#[macro_use]
extern crate libfuzzer_sys;
extern crate compiler;

fuzz_target!(|data: &[u8]| {
    if let Ok(s) = std::str::from_utf8(data) {
        compiler::compile(s.into(), "<fuzz test>".into(), false, false);
    }
});
