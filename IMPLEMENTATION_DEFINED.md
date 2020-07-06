# Implementation Defined parts of the standard

## Is `char` signed or unsigned?

Signed.

## How large are data types on each architecture?

See the `src/arch` folder, excluding `src/arch/mod.rs`.

## How does right-shift behave on negative integers?

It performs an arithmetic shift, keeping the sign of the value.
For example, `-3 >> 1` in binary is `1111...1101 >> 1`,
and shifted right will be `1111...1110`, or `-2`.
This is the same as dividing by two and rounding towards negative infinity.

## Does `inline` do anything?

Currently it is not parsed, see https://github.com/jyn514/rcc/issues/84.
Once it is parsed it will be ignored.

## Does `register` do anything?

No.

## Are there any differences from the C standard?

Yes, hexadecimal constants are not required to have an exponent.
See [the hexponent docs](https://docs.rs/hexponent/latest/hexponent/#differences-from-the-specification) and [#483](https://github.com/jyn514/saltwater/issues/483) for more information.
