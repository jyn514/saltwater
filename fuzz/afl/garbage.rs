#[macro_use]
extern crate afl;
extern crate rcc;

fn main() {
    fuzz!(|data: &[u8]| {
        if let Ok(s) = std::str::from_utf8(data) {
            rcc::compile(s.into(), "<fuzz test>".into(), false, false, false);
        }
    });
}
