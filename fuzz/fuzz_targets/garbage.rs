#![no_main]

use libfuzzer_sys::fuzz_target;
use saltwater::{Opt, compile, initialize_aot_module};

fuzz_target!(|data: &[u8]| {
    let opt = Opt {
        filename: "<fuzz test>".into(),
        ..Default::default()
    };
    let module = initialize_aot_module("<fuzz test>".into());
    if let Ok(s) = std::str::from_utf8(data) {
        compile(module, s.into(), opt);
    }
});
