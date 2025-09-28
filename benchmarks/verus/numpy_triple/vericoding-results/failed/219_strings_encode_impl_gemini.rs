// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): removed ensures from spec function to fix compilation error */
spec fn spec_encode_string(s: Seq<char>) -> Seq<u8>
{
    s.map(|_i, c| c as u8)
}

fn encode_string(s: &Vec<char>) -> (result: Vec<u8>)
    ensures
        result@ == spec_encode_string(s@),
{
    let mut encoded_bytes: Vec<u8> = Vec::new();
    let mut i: usize = 0;
    while i < s.len()
        invariant
            0 <= i <= s.len(),
            encoded_bytes@ == spec_encode_string(s@.subrange(0, i as int)),
        decreases s.len() - i
    {
        encoded_bytes.push(s[i] as u8);
        i = i + 1;
    }
    encoded_bytes
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
{
    /* code modified by LLM (iteration 5): no changes needed; previous failure was a compilation error in a helper */
    let mut result: Vec<Vec<u8>> = Vec::new();
    let mut i: usize = 0;
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            result.len() == i,
            forall|k: int| 0 <= k < i ==> result@[k]@ == spec_encode_string(a@[k]@),
        decreases a.len() - i
    {
        let encoded = encode_string(&a[i]);
        result.push(encoded);
        i = i + 1;
    }
    result
}
// </vc-code>


}
fn main() {}