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
/* helper modified by LLM (iteration 5): Removed problematic vec_u8_new helper */
proof fn lemma_div_mod(x: int, d: int) 
    requires d > 0
    ensures x == d * (x / d) + x % d && 0 <= x % d < d
{
}

proof fn lemma_pow2_nonnegative(n: nat) 
    ensures 0 <= pow2(n)
{
}

spec fn pow2(n: nat) -> int 
    decreases n
{
    if n == 0 { 1 } else { 2 * pow2((n - 1) as nat) }
}

spec fn bit_value(b: bool) -> int {
    if b { 1 } else { 0 }
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
/* code modified by LLM (iteration 5): Added decreases clause to outer loop */
{
    let mut result: Vec<u8> = Vec::new();
    let total_bits = a.len();
    let num_bytes = (total_bits + 7) / 8;
    
    let mut byte_idx: usize = 0;
    while byte_idx < num_bytes
        decreases num_bytes - byte_idx
        invariant
            0 <= byte_idx <= num_bytes,
            result.len() == byte_idx,
            forall|idx: int| 0 <= idx < byte_idx ==> {
                let start_idx = idx * 8;
                let bits_in_byte = if start_idx + 8 <= total_bits { 8 } else { total_bits - start_idx };
                match bitorder {
                    BitOrder::Big => {
                        forall|bit_pos: int| 0 <= bit_pos < bits_in_byte ==> {
                            let bit_value = if a[start_idx + bit_pos] { 1u8 } else { 0u8 };
                            (result[idx] & (1u8 << (7 - bit_pos))) == (bit_value << (7 - bit_pos))
                        }
                    },
                    BitOrder::Little => {
                        forall|bit_pos: int| 0 <= bit_pos < bits_in_byte ==> {
                            let bit_value = if a[start_idx + bit_pos] { 1u8 } else { 0u8 };
                            (result[idx] & (1u8 << bit_pos)) == (bit_value << bit_pos)
                        }
                    }
                }
            }
    {
        let start_bit = byte_idx * 8;
        let bits_in_byte = if start_bit + 8 <= total_bits { 8 } else { total_bits - start_bit };
        
        let mut byte_value: u8 = 0;
        let mut bit_pos: usize = 0;
        
        while bit_pos < bits_in_byte
            invariant
                0 <= bit_pos <= bits_in_byte,
                match bitorder {
                    BitOrder::Big => {
                        forall|pos: int| 0 <= pos < bit_pos ==> {
                            let bit_value = if a[start_bit + pos] { 1u8 } else { 0u8 };
                            (byte_value & (1u8 << (7 - pos))) == (bit_value << (7 - pos))
                        }
                    },
                    BitOrder::Little => {
                        forall|pos: int| 0 <= pos < bit_pos ==> {
                            let bit_value = if a[start_bit + pos] { 1u8 } else { 0u8 };
                            (byte_value & (1u8 << pos)) == (bit_value << pos)
                        }
                    }
                }
        {
            let bit_index = start_bit + bit_pos;
            let bit_val = a[bit_index];
            
            match bitorder {
                BitOrder::Big => {
                    if bit_val {
                        byte_value = byte_value | (1u8 << (7 - bit_pos));
                    }
                },
                BitOrder::Little => {
                    if bit_val {
                        byte_value = byte_value | (1u8 << bit_pos);
                    }
                }
            }
            
            bit_pos = bit_pos + 1;
        }
        
        result.push(byte_value);
        byte_idx = byte_idx + 1;
    }
    
    result
}
// </vc-code>

}
fn main() {}