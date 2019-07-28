// https://en.wikipedia.org/wiki/64-bit_computing#64-bit_data_models
#[allow(non_camel_case_types)]
pub(crate) type SIZE_T = u64;
pub(crate) const SIZE_MAX: SIZE_T = SIZE_T::max_value();

pub(crate) const FLOAT_SIZE: u16 = 4;
pub(crate) const DOUBLE_SIZE: u16 = 8;

pub(crate) const LONG_SIZE: u16 = 8;
pub(crate) const INT_SIZE: u16 = 4;
pub(crate) const SHORT_SIZE: u16 = 2;
pub(crate) const BOOL_SIZE: u16 = 1;

pub(crate) const PTR_SIZE: u16 = 8;

pub(crate) const CHAR_BIT: u16 = 8; // number of bits in a byte
