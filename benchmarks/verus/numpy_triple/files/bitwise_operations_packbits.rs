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
// </vc-helpers>

// <vc-spec>
fn packbits(a: Vec<bool>, bitorder: BitOrder) -> (result: Vec<u8>)
    requires a.len() > 0,
    ensures 
        result.len() == (a.len() + 7) / 8,
        forall|byte_idx: int| 0 <= byte_idx < result.len() ==> {
            let start_idx = byte_idx * 8;
            let bits_in_byte = if start_idx + 8 <= a.len() { 8 } else { a.len() - start_idx };
            match bitorder {
                BitOrder::Big => {

                    forall|bit_pos: int| 0 <= bit_pos < bits_in_byte ==> {
                        let bit_value = if start_idx + bit_pos < a.len() && a[start_idx + bit_pos] { 1u8 } else { 0u8 };
                        (result[byte_idx] & (1u8 << (7 - bit_pos))) == (bit_value << (7 - bit_pos))
                    }
                },
                BitOrder::Little => {

                    forall|bit_pos: int| 0 <= bit_pos < bits_in_byte ==> {
                        let bit_value = if start_idx + bit_pos < a.len() && a[start_idx + bit_pos] { 1u8 } else { 0u8 };
                        (result[byte_idx] & (1u8 << bit_pos)) == (bit_value << bit_pos)
                    }
                }
            }
        }
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}