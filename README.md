# itybity

[![Crates.io](https://img.shields.io/crates/v/itybity.svg)](https://crates.io/crates/itybity)
[![Docs.rs](https://docs.rs/itybity/badge.svg)](https://docs.rs/itybity)
[![CI](https://github.com/sinui0/itybity/workflows/CI/badge.svg)](https://github.com/sinui0/itybity/actions)

An itty bitty crate providing bit iterators and bit iterator accessories.

No dependencies, no unsafe, and `#![no_std]` compatible.

## Summary

This crate provides iterators for iterating over the bits of various types, including integers, slices, and strings.
These iterators can be conveniently accessed via the provided extension traits, eg `ToBits`, `IntoBits`, and `StrToBits`.

The `FromBits` trait provides implementations for parsing types from bit iterators.

## Performance

This crate was not designed with performance in mind, but rather simplicity. For a more performant and memory
efficient alternative, see [`bitvec`](https://docs.rs/bitvec/latest/bitvec/).

That being said, the iterators in this crate are still reasonably fast and compact.

## Bit Order

Be careful not to confuse bit order with byte order (endianness). Bit order refers to the order in which bits are positioned
within a container. See [this wiki](https://en.wikipedia.org/wiki/Bit_numbering) for more information.

Conventionally, bits are written with the least-significant bit on the right. However, when dealing with bit vectors it is often
more intuitive to have the least-significant bit reside at index 0, ie left-most or Lsb0 order.

For example, the number 69 in binary is `01000101`, which translates to the following bit vector in Lsb0:

`[1, 0, 1, 0, 0, 0, 1, 0]`

And the following in Msb0:

`[0, 1, 0, 0, 0, 1, 0, 1]`

## Usage

First, add the following to your `Cargo.toml`:

```toml
[dependencies]
itybity = "0.1"
```

## Examples

```rust
use itybity::{ToBits, IntoBits, FromBits, StrToBits};

let byte = 0b1010_1010u8;

// Convert to a Vec<bool> in Lsb0 order.
let bits = byte.to_lsb0_vec();

assert_eq!(bits, vec![false, true, false, true, false, true, false, true]);

// Writing a bit vector using bools is a pain, use a string instead!
//
// Notice that the string is written in Msb0 order, and we reverse it to Lsb0.
let expected_bits = "10101010".iter_bits().rev().collect::<Vec<bool>>();

assert_eq!(bits, expected_bits);

// Convert back to a u8.
let new_byte = u8::from_lsb0(bits);
assert_eq!(byte, new_byte);

// We can work with slices too!
let bytes = vec![0u8, 1u8, 2u8, 3u8];

// Create an iterator over the bits in Msb0 order.
let bits = bytes.iter_msb0();

assert_eq!(bits.len(), 32);

// Convert back to a different type
let data = u32::from_msb0(bits);

// If we have an iterator of values, we can map it to an iterator of bits.
let iter = vec![0u8, 1u8, 2u8, 3u8].into_iter();

let bit_iter = iter.flat_map(IntoBits::into_iter_lsb0);

// And we can parse it back
let values = Vec::<u8>::from_lsb0(bit_iter);

assert_eq!(values, vec![0u8, 1u8, 2u8, 3u8]);

// We can do the same with arrays. Notice that the array is longer, so the last element
// will be 0.
let values = <[u8; 5]>::from_lsb0(values.iter_lsb0());

assert_eq!(values, [0u8, 1u8, 2u8, 3u8, 0u8]);
```

## Features

`itybty` supports `#[no_std]` by disabling the default features.

- `std`: Enables `alloc`, for use of `Vec` and `String` types.

## License

Licensed under either of

 * Apache License, Version 2.0
   ([LICENSE-APACHE](LICENSE-APACHE) or http://www.apache.org/licenses/LICENSE-2.0)
 * MIT license
   ([LICENSE-MIT](LICENSE-MIT) or http://opensource.org/licenses/MIT)

at your option.

## Contribution

Unless you explicitly state otherwise, any contribution intentionally submitted
for inclusion in the work by you, as defined in the Apache-2.0 license, shall be
dual licensed as above, without any additional terms or conditions.

See [CONTRIBUTING.md](CONTRIBUTING.md).
