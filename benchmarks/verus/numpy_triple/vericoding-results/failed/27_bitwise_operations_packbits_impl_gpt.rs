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
/* helper modified by LLM (iteration 2): simplified helper (not directly used) */
fn min(a: int, b: int) -> int { if a < b { a } else { b } }
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
    /* code modified by LLM (iteration 2): reimplemented loop without Verus invariants and using safe shifts */
    let a_len = a.len();
    let nbytes: usize = (a_len + 7) / 8;
    let mut result: Vec<u8> = Vec::new();
    let mut i: usize = 0;
    while i < nbytes {
        let start_idx: usize = i * 8;
        let bits_in_byte: usize = if start_idx + 8 <= a_len { 8 } else { a_len - start_idx };
        let mut b: u8 = 0u8;
        match bitorder {
            BitOrder::Big => {
                let mut p: usize = 0;
                while p < bits_in_byte {
                    let shift: u32 = (7 - p) as u32;
                    let mask: u8 = 1u8 << shift;
                    if a[start_idx + p] {
                        b |= mask;
                    } else {
                        b &= !mask;
                    }
                    p += 1;
                }
            }
            BitOrder::Little => {
                let mut p: usize = 0;
                while p < bits_in_byte {
                    let shift: u32 = p as u32;
                    let mask: u8 = 1u8 << shift;
                    if a[start_idx + p] {
                        b |= mask;
                    } else {
                        b &= !mask;
                    }
                    p += 1;
                }
            }
        }
        result.push(b);
        i += 1;
    }
    result
}
// </vc-code>

}
fn main() {}