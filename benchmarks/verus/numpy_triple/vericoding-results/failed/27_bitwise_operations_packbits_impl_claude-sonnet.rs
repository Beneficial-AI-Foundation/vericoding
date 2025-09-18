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
/* helper modified by LLM (iteration 5): added bounds checking and cast safety for arithmetic operations */
fn pack_byte_big_endian(bits: &Vec<bool>, start_idx: usize, bits_in_byte: usize) -> (result: u8)
    requires 
        start_idx + bits_in_byte <= bits.len(),
        bits_in_byte <= 8,
        start_idx < bits.len()
    ensures
        forall|bit_pos: int| #![trigger (result & (1u8 << (7 - bit_pos)))] 0 <= bit_pos < bits_in_byte ==> {
            let bit_value = if start_idx + bit_pos < bits.len() && bits[start_idx + bit_pos] { 1u8 } else { 0u8 };
            (result & (1u8 << (7 - bit_pos))) == (bit_value << (7 - bit_pos))
        }
{
    let mut byte_val: u8 = 0;
    let mut i: usize = 0;
    while i < bits_in_byte
        invariant
            0 <= i <= bits_in_byte,
            bits_in_byte <= 8,
            start_idx + bits_in_byte <= bits.len(),
            forall|bit_pos: int| #![trigger (byte_val & (1u8 << (7 - bit_pos)))] 0 <= bit_pos < i ==> {
                let bit_value = if start_idx + bit_pos < bits.len() && bits[start_idx + bit_pos] { 1u8 } else { 0u8 };
                (byte_val & (1u8 << (7 - bit_pos))) == (bit_value << (7 - bit_pos))
            }
        decreases bits_in_byte - i
    {
        if start_idx + i < bits.len() && bits[start_idx + i] {
            proof {
                assert(i < 8);
                assert(7 - i >= 0);
                assert(7 - i < 8);
            }
            byte_val = byte_val | (1u8 << ((7 - i) as u8));
        }
        i += 1;
    }
    byte_val
}

fn pack_byte_little_endian(bits: &Vec<bool>, start_idx: usize, bits_in_byte: usize) -> (result: u8)
    requires 
        start_idx + bits_in_byte <= bits.len(),
        bits_in_byte <= 8,
        start_idx < bits.len()
    ensures
        forall|bit_pos: int| #![trigger (result & (1u8 << bit_pos))] 0 <= bit_pos < bits_in_byte ==> {
            let bit_value = if start_idx + bit_pos < bits.len() && bits[start_idx + bit_pos] { 1u8 } else { 0u8 };
            (result & (1u8 << bit_pos)) == (bit_value << bit_pos)
        }
{
    let mut byte_val: u8 = 0;
    let mut i: usize = 0;
    while i < bits_in_byte
        invariant
            0 <= i <= bits_in_byte,
            bits_in_byte <= 8,
            start_idx + bits_in_byte <= bits.len(),
            forall|bit_pos: int| #![trigger (byte_val & (1u8 << bit_pos))] 0 <= bit_pos < i ==> {
                let bit_value = if start_idx + bit_pos < bits.len() && bits[start_idx + bit_pos] { 1u8 } else { 0u8 };
                (byte_val & (1u8 << bit_pos)) == (bit_value << bit_pos)
            }
        decreases bits_in_byte - i
    {
        if start_idx + i < bits.len() && bits[start_idx + i] {
            proof {
                assert(i < 8);
            }
            byte_val = byte_val | (1u8 << (i as u8));
        }
        i += 1;
    }
    byte_val
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
    /* code modified by LLM (iteration 5): fixed arithmetic overflow checks and preconditions */
    proof {
        assert(a.len() > 0);
        assert(a.len() + 7 >= 7);
        assert((a.len() + 7) / 8 >= 1);
    }
    
    let num_bytes = (a.len() + 7) / 8;
    let mut result: Vec<u8> = Vec::with_capacity(num_bytes);
    
    let mut byte_idx: usize = 0;
    while byte_idx < num_bytes
        invariant
            0 <= byte_idx <= num_bytes,
            result.len() == byte_idx,
            num_bytes == (a.len() + 7) / 8,
            num_bytes > 0,
            a.len() > 0,
            forall|bi: int| #![trigger result[bi]] 0 <= bi < byte_idx ==> {
                let start_idx = bi * 8;
                let bits_in_byte = if start_idx + 8 <= a.len() { 8 } else { a.len() - start_idx };
                match bitorder {
                    BitOrder::Big => {
                        forall|bit_pos: int| #![trigger (result[bi] & (1u8 << (7 - bit_pos)))] 0 <= bit_pos < bits_in_byte ==> {
                            let bit_value = if start_idx + bit_pos < a.len() && a[start_idx + bit_pos] { 1u8 } else { 0u8 };
                            (result[bi] & (1u8 << (7 - bit_pos))) == (bit_value << (7 - bit_pos))
                        }
                    },
                    BitOrder::Little => {
                        forall|bit_pos: int| #![trigger (result[bi] & (1u8 << bit_pos))] 0 <= bit_pos < bits_in_byte ==> {
                            let bit_value = if start_idx + bit_pos < a.len() && a[start_idx + bit_pos] { 1u8 } else { 0u8 };
                            (result[bi] & (1u8 << bit_pos)) == (bit_value << bit_pos)
                        }
                    }
                }
            }
        decreases num_bytes - byte_idx
    {
        let start_idx = byte_idx * 8;
        let bits_in_byte = if start_idx + 8 <= a.len() { 8 } else { a.len() - start_idx };
        
        proof {
            assert(byte_idx < num_bytes);
            assert(start_idx < a.len());
            assert(start_idx + bits_in_byte <= a.len());
            assert(bits_in_byte <= 8);
        }
        
        let byte_val = match bitorder {
            BitOrder::Big => pack_byte_big_endian(&a, start_idx, bits_in_byte),
            BitOrder::Little => pack_byte_little_endian(&a, start_idx, bits_in_byte)
        };
        
        result.push(byte_val);
        byte_idx += 1;
    }
    
    result
}
// </vc-code>

}
fn main() {}