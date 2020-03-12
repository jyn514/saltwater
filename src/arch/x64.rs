use super::Archictecture;

struct x86_64;
impl Archictecture for x86_64 {
    // https://en.wikipedia.org/wiki/64-bit_computing#64-bit_data_models
    #[allow(non_camel_case_types)]
    type SIZE_T = u64;
    const SIZE_MAX: u64 = u64::max_value();
}