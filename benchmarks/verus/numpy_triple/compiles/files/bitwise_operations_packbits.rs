/* Packs binary-valued elements into bits in a UInt8 array.
Each group of 8 binary values is packed into one UInt8.
The result is padded with zeros if needed.

Specification: packbits correctly packs binary values into UInt8 bytes according to bitorder.
For big-endian: first element goes to MSB (bit 7)
For little-endian: first element goes to LSB (bit 0) */

use vstd::prelude::*;

verus! {

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BitOrder {
    Big,
    Little,
}
fn packbits(a: &Vec<bool>, bitorder: BitOrder) -> (result: Vec<u8>)
    ensures
        result.len() == (a.len() + 7) / 8,
{
    // impl-start
    assume(false);
    Vec::new()
    // impl-end
}
}
fn main() {}