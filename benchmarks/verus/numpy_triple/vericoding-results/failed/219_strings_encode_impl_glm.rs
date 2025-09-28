// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
fn encode_char(c: char) -> (bytes: Vec<u8>)
    ensures
        bytes.len() == 1,
{
    vec![(c as u32) as u8]
}

fn encode_string(s: Vec<char>) -> (bytes: Vec<u8>)
    ensures
        bytes.len() == s.len(),
{
    let mut result = Vec::new();
    let mut i: nat = 0;
    while i < s.len()
        invariant
            0 <= i <= s.len(),
            result.len() == i,
    {
        let c = s[i];
        let encoded = encode_char(c);
        result.push(encoded[0]);
        i += 1;
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
{
    /* code modified by LLM (iteration 5): fixed type mismatch in loop condition */
    let a_seq = a@;
    let mut result: Vec<Vec<u8>> = Vec::new();
    let mut iter = a.into_iter();
    let mut i: nat = 0;
    while i < a_seq.len() as nat
        invariant
            0 <= i <= a_seq.len(),
            result.len() == i,
            forall |j: int| 0 <= j < i ==> 
                (a_seq[j].len() == 0 ==> result@[j].len() == 0) &&
                (a_seq[j].len() > 0 ==> result@[j].len() > 0) &&
                (result@[j].len() >= a_seq[j].len())
        decreases (a_seq.len() - i)
    {
        let s = iter.next().unwrap();
        let encoded = encode_string(s);
        result.push(encoded);
        i += 1;
    }
    result
}
// </vc-code>


}
fn main() {}