use vstd::prelude::*;

verus! {

spec fn encode_char_spec(c: int) -> (result:int)
    recommends
        65 <= c <= 90,
{
    (c - 65 + 5) % 26 + 65
}
// pure-end
spec fn decode_char_spec(c: int) -> (result:int)
    recommends
        65 <= c <= 90,
{
    (c - 65 + 26 - 5) % 26 + 65
}
// pure-end

// <vc-helpers>
// As the SPEC and PREAMBLE already contain the necessary spec functions (encode_char_spec and decode_char_spec), 
// no additional helpers or proofs are required in this section for the verification of the implementation.
// The decoding logic is directly implemented using the provided spec functions in the loop.
// </vc-helpers>

// <vc-spec>
#[verifier::loop_isolation(false)]
fn decode_shift(s: &Vec<u8>) -> (t: Vec<u8>)
    // pre-conditions-start
    requires
        forall|i: int| #![trigger s[i]] 0 <= i < s.len() ==> 65 <= s[i] <= 90,
    // pre-conditions-end
    // post-conditions-start
    ensures
        s.len() == t.len(),
        forall|i: int| #![auto] 0 <= i < t.len() ==> t[i] == decode_char_spec(s[i] as int),
        forall|i: int| #![auto] 0 <= i < t.len() ==> encode_char_spec(t[i] as int) == s[i],
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
    let mut t: Vec<u8> = Vec::new();
    let mut i: usize = 0;
    while i < s.len()
        invariant
            0 <= i <= s.len(),
            i <= usize::MAX,
            t.len() == i,
            forall|k: int| 0 <= k < i ==> #[trigger] t[k] == decode_char_spec(s[k] as int),
            forall|k: int| 0 <= k < i ==> #[trigger] encode_char_spec(t[k] as int) == s[k]
    {
        let c = s[i];
        let decoded: u8 = ((c as int - 65 + 26 - 5) % 26 + 65) as u8;
        t.push(decoded);
        i += 1;
    }
    t
}
// </vc-code>

fn main() {}
}