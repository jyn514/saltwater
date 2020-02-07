#![no_main]
#[macro_use]
extern crate libfuzzer_sys;
extern crate rcc;

fuzz_target!(|data: &[u8]| {
    let opt = rcc::Opt {
        filename: "<fuzz test>".into(),
        ..Default::default()
    };
    if let Ok(s) = std::str::from_utf8(data) {
        rcc::compile(s.into(), &opt);
    }
});
