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
/* helper modified by LLM (iteration 5): kept as is, helpers are correct */
spec fn compute_byte(a: Seq<bool>, start_idx: nat, bits_in_byte: nat, bitorder: BitOrder) -> u8
    requires
        bits_in_byte <= 8,
        start_idx + bits_in_byte <= a.len(),
    decreases bits_in_byte
{
    if bits_in_byte == 0 {
        0
    } else {
        let bit_idx = start_idx + (bits_in_byte - 1);
        let bit_value: u8 = if a[bit_idx] { 1 } else { 0 };
        let shift_val: int = if bitorder == BitOrder::Big { 7 - ((bits_in_byte - 1) as int) } else { (bits_in_byte - 1) as int };
        let shift: u8 = shift_val as u8;
        compute_byte(a, start_idx, (bits_in_byte - 1) as nat, bitorder) | (bit_value << shift)
    }
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
/* code modified by LLM (iteration 5): inlined let assignments in invariant to fix compilation error */
{
    let a_seq = a@;
    let a_len = a.len() as int;
    let num_bytes: int = (a_len + 7) / 8;
    let mut result: Vec<u8> = Vec::with_capacity(num_bytes as usize);
    let mut byte_idx = 0;
    while byte_idx < num_bytes
        invariant
            0 <= byte_idx <= num_bytes,
            result.len() == byte_idx as usize,
            forall|i: int| 0 <= i < byte_idx ==> result[i] == compute_byte(a_seq, (i*8) as nat, if (i*8 + 8) <= a_len { 8 as nat } else { (a_len - i*8) as nat }, bitorder)
    {
        let start_idx: int = byte_idx * 8;
        let bits_in_byte: nat = if start_idx + 8 <= a_len { 8 as nat } else { (a_len - start_idx) as nat };
        let mut val: u8 = 0;
        let mut bit_pos = 0;
        while bit_pos < bits_in_byte as int
            invariant
                0 <= bit_pos <= bits_in_byte as int,
                val == compute_byte(a_seq, start_idx as nat, bit_pos as nat, bitorder),
                0 <= start_idx <= a_len - bits_in_byte as int
        {
            let idx = (start_idx + bit_pos) as usize;
            if a[idx] {
                let shift: int = if bitorder == BitOrder::Big {
                    7 - bit_pos
                } else {
                    bit_pos
                };
                val |= 1u8 << (shift as u32);
            }
            bit_pos += 1;
        }
        result.push(val);
        byte_idx += 1;
    }
    result
}
// </vc-code>

}
fn main() {}