// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn encode_char_spec(c: int) -> (result:int)
    recommends
        65 <= c <= 90,
{
    (c - 65 + 5) % 26 + 65
}
spec fn decode_char_spec(c: int) -> (result:int)
    recommends
        65 <= c <= 90,
{
    (c - 65 + 26 - 5) % 26 + 65
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): Added encode_decode_inverse proof function */
proof fn encode_decode_inverse(c: int)
    requires
        65 <= c <= 90
    ensures
        decode_char_spec(encode_char_spec(c)) == c,
        encode_char_spec(decode_char_spec(c)) == c
{
    assert((c - 65 + 5) % 26 >= 0);
    assert((c - 65 + 5) % 26 < 26);
    assert((c - 65 + 26 - 5) % 26 >= 0);
    assert((c - 65 + 26 - 5) % 26 < 26);
    let encoded = (c - 65 + 5) % 26 + 65;
    let decoded = (encoded - 65 + 26 - 5) % 26 + 65;
    assert(decoded == ((((c - 65 + 5) % 26 + 65) - 65 + 26 - 5) % 26 + 65));
    assert(decoded == ((((c - 65 + 5) % 26) + 26 - 5) % 26 + 65));
    assert(decoded == (((c - 65 + 5) % 26 + 21) % 26 + 65));
    assert((c - 65 + 5) % 26 + 21 == (c - 65 + 5) % 26 + 21);
    assert(((c - 65 + 5) % 26 + 21) % 26 == (c - 65) % 26);
    assert(decoded == (c - 65) % 26 + 65);
    assert(decoded == c);
}
// </vc-helpers>

// <vc-spec>
#[verifier::loop_isolation(false)]
fn decode_shift(s: &Vec<u8>) -> (t: Vec<u8>)

    requires
        forall|i: int| #![trigger s[i]] 0 <= i < s.len() ==> 65 <= s[i] <= 90,

    ensures
        s.len() == t.len(),
        forall|i: int| #![auto] 0 <= i < t.len() ==> t[i] == decode_char_spec(s[i] as int),
        forall|i: int| #![auto] 0 <= i < t.len() ==> encode_char_spec(t[i] as int) == s[i],
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): Added decreases clause to while loop */
    let mut t = Vec::new();
    let mut i: usize = 0;
    while i < s.len()
        invariant
            0 <= i <= s.len(),
            t.len() == i,
            forall|j: int| #![auto] 0 <= j < i ==> t[j] == decode_char_spec(s[j] as int),
            forall|j: int| #![auto] 0 <= j < i ==> encode_char_spec(t[j] as int) == s[j],
        decreases s.len() - i
    {
        let c = s[i];
        let decoded = ((c - 65 + 26 - 5) % 26 + 65) as u8;
        t.push(decoded);
        proof {
            encode_decode_inverse(c as int);
        }
        i = i + 1;
    }
    t
}
// </vc-code>

}
fn main() {}