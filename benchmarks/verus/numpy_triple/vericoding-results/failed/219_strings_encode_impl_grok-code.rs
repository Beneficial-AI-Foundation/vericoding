// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): added invariants to ensure length postcondition, changed for loop to while loop with invariants, added truncate to casts */
fn encode_string(s: Vec<char>) -> (result: Vec<u8>)
    requires true,
    ensures
        result@.len() >= s@.len(),
        if s@.len() == 0 { result@.len() == 0 } else { true },
{
    let mut result = Vec::new();
    let mut index: usize = 0;
    while index < s.len()
        invariant
            0 <= index <= s@.len(),
            result@.len() >= index,
        decreases s@.len() - index
    {
        let c = s[index];
        let code = c as u32;
        let bytes = if code <= 0x7f_u32 {
            let mut v = Vec::new();
            v.push(#[verifier::truncate] (code as u8));
            v
        } else if code <= 0x7ff_u32 {
            let mut v = Vec::new();
            v.push(0xc0_u8 | #[verifier::truncate] ((code >> 6) as u8));
            v.push(0x80_u8 | #[verifier::truncate] ((code & 63) as u8));
            v
        } else if code <= 0xffff_u32 {
            let mut v = Vec::new();
            v.push(0xe0_u8 | #[verifier::truncate] ((code >> 12) as u8));
            v.push(0x80_u8 | #[verifier::truncate] (((code >> 6) & 63) as u8));
            v.push(0x80_u8 | #[verifier::truncate] ((code & 63) as u8));
            v
        } else {
            let mut v = Vec::new();
            v.push(0xf0_u8 | #[verifier::truncate] ((code >> 18) as u8));
            v.push(0x80_u8 | #[verifier::truncate] (((code >> 12) & 63) as u8));
            v.push(0x80_u8 | #[verifier::truncate] (((code >> 6) & 63) as u8));
            v.push(0x80_u8 | #[verifier::truncate] ((code & 63) as u8));
            v
        };
        let mut bytes_index = 0;
        proof {
            assert(bytes@.len() >= 1);
        }
        while bytes_index < bytes.len()
            invariant
                0 <= bytes_index <= bytes@.len(),
        {
            result.push(bytes[bytes_index]);
            bytes_index += 1;
        }
        index += 1;
    }
    result
}
// </vc-helpers>

// <vc-spec>
fn encode(a: Vec<Vec<char>>, encoding: Vec<char>, errors: Vec<char>) -> (result: Vec<Vec<u8>>)
    ensures
        result@.len() == a@.len(),
        /* Deterministic encoding: same input produces same output */
        forall|i: int, j: int| 0 <= i < a@.len() && 0 <= j < a@.len() && a@[i] == a@[j] ==> result@[i] == result@[j],
        /* Empty strings encode to empty byte arrays */
        forall|i: int| 0 <= i < a@.len() && a@[i].len() == 0 ==> result@[i].len() == 0,
        /* Non-empty strings produce non-empty byte arrays */
        forall|i: int| 0 <= i < a@.len() && a@[i].len() > 0 ==> result@[i].len() > 0,
        /* For UTF-8 encoding, encoded size is at least the string length */
        forall|i: int| 0 <= i < a@.len() ==> result@[i].len() >= a@[i].len(),
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): added proof assertion for result length */
{
    let mut result: Vec<Vec<u8>> = Vec::new();
    for i in 0..a.len() {
        let encoded = encode_string(a[i].clone());
        result.push(encoded);
    }
    proof {
        assert(result@.len() == a@.len());
    }
    result
}
// </vc-code>


}
fn main() {}