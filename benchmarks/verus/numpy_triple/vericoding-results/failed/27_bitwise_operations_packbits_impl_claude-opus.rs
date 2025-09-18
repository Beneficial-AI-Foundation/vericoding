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
proof fn lemma_shift_or_preserves_bits(byte: u8, bit_pos: int, bit_value: bool)
    requires 0 <= bit_pos < 8
    ensures
        bit_value ==> ((byte | (1u8 << bit_pos)) & (1u8 << bit_pos)) == (1u8 << bit_pos),
        !bit_value ==> ((byte | (0u8 << bit_pos)) & (1u8 << bit_pos)) == (byte & (1u8 << bit_pos))
{
    assert(0u8 << bit_pos == 0u8);
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
    /* code modified by LLM (iteration 5): Added trigger annotations to quantifiers in invariants */
    let num_bytes = (a.len() + 7) / 8;
    let mut result: Vec<u8> = Vec::new();
    
    let mut byte_idx = 0;
    while byte_idx < num_bytes
        invariant
            byte_idx <= num_bytes,
            result.len() == byte_idx,
            forall|i: int| #![trigger result[i]] 0 <= i < byte_idx ==> {
                let start_idx = i * 8;
                let bits_in_byte = if start_idx + 8 <= a.len() { 8 } else { a.len() - start_idx };
                match bitorder {
                    BitOrder::Big => {
                        forall|bit_pos: int| #![trigger a[start_idx + bit_pos]] 0 <= bit_pos < bits_in_byte ==> {
                            let bit_value = if start_idx + bit_pos < a.len() && a[start_idx + bit_pos] { 1u8 } else { 0u8 };
                            (result[i] & (1u8 << (7 - bit_pos))) == (bit_value << (7 - bit_pos))
                        }
                    },
                    BitOrder::Little => {
                        forall|bit_pos: int| #![trigger a[start_idx + bit_pos]] 0 <= bit_pos < bits_in_byte ==> {
                            let bit_value = if start_idx + bit_pos < a.len() && a[start_idx + bit_pos] { 1u8 } else { 0u8 };
                            (result[i] & (1u8 << bit_pos)) == (bit_value << bit_pos)
                        }
                    }
                }
            },
        decreases num_bytes - byte_idx
    {
        let start_idx = byte_idx * 8;
        let mut byte: u8 = 0;
        let mut bit_idx = 0;
        
        while bit_idx < 8 && start_idx + bit_idx < a.len()
            invariant
                0 <= bit_idx <= 8,
                start_idx + bit_idx <= a.len(),
                match bitorder {
                    BitOrder::Big => {
                        forall|j: int| #![trigger byte, j] 0 <= j < bit_idx ==> {
                            let bit_value = if a[start_idx + j] { 1u8 } else { 0u8 };
                            (byte & (1u8 << (7 - j))) == (bit_value << (7 - j))
                        }
                    },
                    BitOrder::Little => {
                        forall|j: int| #![trigger byte, j] 0 <= j < bit_idx ==> {
                            let bit_value = if a[start_idx + j] { 1u8 } else { 0u8 };
                            (byte & (1u8 << j)) == (bit_value << j)
                        }
                    }
                },
            decreases 8 - bit_idx
        {
            if a[start_idx + bit_idx] {
                match bitorder {
                    BitOrder::Big => {
                        byte = byte | (1u8 << (7 - bit_idx));
                        proof {
                            lemma_shift_or_preserves_bits(byte, (7 - bit_idx) as int, true);
                        }
                    },
                    BitOrder::Little => {
                        byte = byte | (1u8 << bit_idx);
                        proof {
                            lemma_shift_or_preserves_bits(byte, bit_idx as int, true);
                        }
                    }
                }
            }
            bit_idx = bit_idx + 1;
        }
        
        result.push(byte);
        byte_idx = byte_idx + 1;
    }
    
    result
}
// </vc-code>

}
fn main() {}