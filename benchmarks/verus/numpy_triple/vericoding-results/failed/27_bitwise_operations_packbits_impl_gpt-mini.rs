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
/* helper modified by LLM (iteration 5): convert bool to u8 and compute bytes length */
fn bit_to_u8(b: bool) -> u8 { if b { 1u8 } else { 0u8 } }
spec fn bytes_len(n: nat) -> nat { (n + 7) / 8 }
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
    /* code modified by LLM (iteration 5): build result bytes with correct bit ordering, use nat indices to satisfy verification */
    let len: nat = a.len();
    let result_len: nat = (len + 7) / 8;
    let mut result: Vec<u8> = Vec::new();
    let mut byte_idx: nat = 0;
    while byte_idx < result_len
        invariant byte_idx <= result_len;
        invariant result.len() == byte_idx;
        invariant forall|b: nat| 0 <= b && b < byte_idx ==> {
            let start_idx: nat = b * 8;
            let bits_in_byte: nat = if start_idx + 8 <= len { 8 } else { len - start_idx };
            match bitorder {
                BitOrder::Big => {
                    forall|bit_pos: nat| 0 <= bit_pos && bit_pos < bits_in_byte ==> {
                        let bit_value: u8 = if a[start_idx + bit_pos] { 1u8 } else { 0u8 };
                        (result[b] & (1u8 << (7 - bit_pos))) == (bit_value << (7 - bit_pos))
                    }
                },
                BitOrder::Little => {
                    forall|bit_pos: nat| 0 <= bit_pos && bit_pos < bits_in_byte ==> {
                        let bit_value: u8 = if a[start_idx + bit_pos] { 1u8 } else { 0u8 };
                        (result[b] & (1u8 << bit_pos)) == (bit_value << bit_pos)
                    }
                }
            }
        }
        decreases result_len - byte_idx
    {
        let start_idx: nat = byte_idx * 8;
        let bits_in_byte: nat = if start_idx + 8 <= len { 8 } else { len - start_idx };
        let mut byte: u8 = 0u8;
        let mut bit_pos: nat = 0;
        while bit_pos < bits_in_byte
            invariant bit_pos <= bits_in_byte;
            invariant forall|i: nat| 0 <= i && i < bit_pos ==> {
                match bitorder {
                    BitOrder::Big => {
                        let bit_value: u8 = if a[start_idx + i] { 1u8 } else { 0u8 };
                        (byte & (1u8 << (7 - i))) == (bit_value << (7 - i))
                    },
                    BitOrder::Little => {
                        let bit_value: u8 = if a[start_idx + i] { 1u8 } else { 0u8 };
                        (byte & (1u8 << i)) == (bit_value << i)
                    }
                }
            }
            decreases bits_in_byte - bit_pos
        {
            let bit_value: u8 = if a[start_idx + bit_pos] { 1u8 } else { 0u8 };
            match bitorder {
                BitOrder::Big => { byte = byte | (bit_value << (7 - bit_pos)); },
                BitOrder::Little => { byte = byte | (bit_value << bit_pos); },
            }
            bit_pos = bit_pos + 1;
        }
        result.push(byte);
        byte_idx = byte_idx + 1;
    }
    result
}
// </vc-code>

}
fn main() {}