#[macro_use]
extern crate afl;
extern crate compiler;

fn main() {
    fuzz!(|data: &[u8]| {
        if let Ok(s) = std::str::from_utf8(data) {
            compiler::compile(s.into(), "<fuzz test>".into(), false, false, false);
        }
    });
}
