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
/* helper modified by LLM (iteration 5): Corrected `get_bit` implementation. The `arr[idx]` for a `Vec<bool>` expects a `usize` index for the concrete type, not `int` which is for the ghost type. */
spec fn get_bit(arr: &Vec<bool>, idx: usize) -> u8 {
    if idx < arr.len() && arr[idx] { 1u8 } else { 0u8 }
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
/* code modified by LLM (iteration 5): Fixed `a[original_bit_idx as int]` to `a[original_bit_idx]` to address the compilation error, as `original_bit_idx` is already `usize` and `a` is a concrete `Vec<bool>` which expects `usize` indexing. */
{
    let num_bytes: usize = (a.len() / 8) + (if a.len() % 8 != 0 { 1 } else { 0 });
    let mut result: Vec<u8> = Vec::new();
    result.reserve(num_bytes);
    for _ in 0..num_bytes {
        result.push(0u8);
    }

    if a.len() == 0usize { return result; }

    let mut byte_idx: usize = 0usize;
    while byte_idx < num_bytes
        invariant
            byte_idx <= num_bytes,
            result.len() == num_bytes,
            forall|k: int| 0 <= k < byte_idx ==> {
                let start_idx: usize = (k as usize) * 8;
                let bits_in_byte: usize = if start_idx + 8 <= a.len() { 8 } else { a.len() - start_idx };
                match bitorder {
                    BitOrder::Big => {
                        forall|bit_pos: int| 0 <= bit_pos < (bits_in_byte as int) ==> {
                            let bit_value = get_bit(&a, start_idx + (bit_pos as usize));
                            (result[k as int] & (1u8 << (7 - (bit_pos as usize)))) == (bit_value << (7 - (bit_pos as usize)))
                        }
                    },
                    BitOrder::Little => {
                        forall|bit_pos: int| 0 <= bit_pos < (bits_in_byte as int) ==> {
                            let bit_value = get_bit(&a, start_idx + (bit_pos as usize));
                            (result[k as int] & (1u8 << (bit_pos as usize))) == (bit_value << (bit_pos as usize))
                        }
                    }
                }
            }
    {
        let start_idx: usize = byte_idx * 8;
        let bits_in_byte: usize = if start_idx + 8 <= a.len() { 8 } else { a.len() - start_idx };
        let mut current_byte: u8 = 0;

        let mut bit_pos: usize = 0usize;
        while bit_pos < bits_in_byte
            invariant
                bit_pos <= bits_in_byte,
                byte_idx < num_bytes,
                result.len() == num_bytes,
                match bitorder {
                    BitOrder::Big => {
                        forall|k: int| 0 <= k < (bit_pos as int) ==> {
                            let bit_value = get_bit(&a, start_idx + (k as usize));
                            (current_byte & (1u8 << (7usize - (k as usize)))) == (bit_value << (7usize - (k as usize)))
                        }
                    },
                    BitOrder::Little => {
                        forall|k: int| 0 <= k < (bit_pos as int) ==> {
                            let bit_value = get_bit(&a, start_idx + (k as usize));
                            (current_byte & (1u8 << (k as usize))) == (bit_value << (k as usize))
                        }
                    }
                }
        {
            let original_bit_idx: usize = start_idx + bit_pos;
            if original_bit_idx < a.len() && a[original_bit_idx] {
                match bitorder {
                    BitOrder::Big => {
                        current_byte |= (1u8 << (7usize - bit_pos));
                    },
                    BitOrder::Little => {
                        current_byte |= (1u8 << bit_pos);
                    }
                }
            }
            bit_pos = bit_pos + 1;
        }
        result.set(byte_idx, current_byte);
        byte_idx = byte_idx + 1;
    }
    result
}
// </vc-code>

}
fn main() {}