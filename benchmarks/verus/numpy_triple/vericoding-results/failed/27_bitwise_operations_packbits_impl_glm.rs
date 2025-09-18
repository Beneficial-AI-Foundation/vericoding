// <vc-preamble>
use vstd::prelude::*;

verus! {

#[derive(PartialEq, Eq)]
enum BitOrder {
    Big,
    Little
}
// </vc-preamble>

// <vc-helpers>
fn packbits_helper(bits: &Vec<bool>, start_idx: int, bits_in_byte: int, bitorder: BitOrder) -> (result: u8)
    requires 0 <= start_idx < bits.len() && 0 < bits_in_byte <= 8 && start_idx + bits_in_byte <= bits.len(),
    ensures
        match bitorder {
            BitOrder::Big => {
                forall|bit_pos: int| 0 <= bit_pos < bits_in_byte ==> {
                    let bit_value = if bits@[start_idx + bit_pos] { 1u8 } else { 0u8 };
                    (result & (1u8 << (7 - bit_pos))) == (bit_value << (7 - bit_pos))
                }
            },
            BitOrder::Little => {
                forall|bit_pos: int| 0 <= bit_pos < bits_in_byte ==> {
                    let bit_value = if bits@[start_idx + bit_pos] { 1u8 } else { 0u8 };
                    (result & (1u8 << bit_pos)) == (bit_value << bit_pos)
                }
            }
        }
{
    let mut result: u8 = 0;
    if bitorder == BitOrder::Big {
        for bit_pos in 0..bits_in_byte
            invariant 0 <= bit_pos <= bits_in_byte,
            invariant forall|i: int| 0 <= i < bit_pos ==> {
                let bit_value = if bits@[start_idx + i] { 1u8 } else { 0u8 };
                (result & (1u8 << (7 - i))) == (bit_value << (7 - i))
            }
        {
            if bits@[start_idx + bit_pos] {
                result = result | (1u8 << (7 - (bit_pos as int)));
            }
        }
    } else {
        for bit_pos in 0..bits_in_byte
            invariant 0 <= bit_pos <= bits_in_byte,
            invariant forall|i: int| 0 <= i < bit_pos ==> {
                let bit_value = if bits@[start_idx + i] { 1u8 } else { 0u8 };
                (result & (1u8 << i)) == (bit_value << i)
            }
        {
            if bits@[start_idx + bit_pos] {
                result = result | (1u8 << (bit_pos as int));
            }
        }
    }
    result
}
// </vc-helpers>

// <vc-spec>
fn packbits(a: Vec<bool>, bitorder: BitOrder) -> (result: Vec<u8>)
    requires a.len() > 0,
    ensures 
        result.len() == (a.len() + 7) / 8,
        forall|byte_idx: int| #![trigger result[byte_idx]] 0 <= byte_idx < result.len() ==> {
            let start_idx = byte_idx * 8;
            let bits_in_byte = if start_idx + 8 <= a.len() { 8 } else { a.len() - start_idx };
            match bitorder {
                BitOrder::Big => {

                    forall|bit_pos: int| #![trigger a[start_idx + bit_pos]] 0 <= bit_pos < bits_in_byte ==> {
                        let bit_value = if start_idx + bit_pos < a.len() && a[start_idx + bit_pos] { 1u8 } else { 0u8 };
                        (result[byte_idx] & (1u8 << (7 - bit_pos))) == (bit_value << (7 - bit_pos))
                    }
                },
                BitOrder::Little => {

                    forall|bit_pos: int| #![trigger a[start_idx + bit_pos]] 0 <= bit_pos < bits_in_byte ==> {
                        let bit_value = if start_idx + bit_pos < a.len() && a[start_idx + bit_pos] { 1u8 } else { 0u8 };
                        (result[byte_idx] & (1u8 << bit_pos)) == (bit_value << bit_pos)
                    }
                }
            }
        }
// </vc-spec>
// <vc-code>
{
    let total_bytes = (a.len() + 7) / 8;
    let mut result = Vec::with_capacity(total_bytes);
    
    for byte_idx in 0..total_bytes
        invariant 0 <= byte_idx <= total_bytes,
        invariant result.len() == byte_idx,
        invariant forall|i: int| 0 <= i < byte_idx ==> {
            let start_idx = i * 8;
            let bits_in_byte = if start_idx + 8 <= a.len() { 8 } else { a.len() - start_idx };
            result[i] == packbits_helper(&a, start_idx, bits_in_byte, bitorder)
        }
    {
        let start_idx = byte_idx * 8;
        let bits_in_byte = if start_idx + 8 <= a.len() { 8 } else { a.len() - start_idx };
        let byte_value = packbits_helper(&a, start_idx, bits_in_byte, bitorder);
        result.push(byte_value);
    }
    
    result
}
// </vc-code>

}
fn main() {}