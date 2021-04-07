//! https://en.wikipedia.org/wiki/64-bit_computing#64-bit_data_models
#![allow(missing_docs)]

#[allow(non_camel_case_types)]
pub type SIZE_T = u64;
#[allow(dead_code)]
pub const SIZE_MAX: SIZE_T = SIZE_T::MAX;

pub const FLOAT_SIZE: u16 = 4;
pub const DOUBLE_SIZE: u16 = 8;

pub const LONG_SIZE: u16 = 8;
pub const INT_SIZE: u16 = 4;
pub const SHORT_SIZE: u16 = 2;
pub const BOOL_SIZE: u16 = 1;

pub const PTR_SIZE: u16 = 8;

pub const CHAR_BIT: u16 = 8; // number of bits in a byte
