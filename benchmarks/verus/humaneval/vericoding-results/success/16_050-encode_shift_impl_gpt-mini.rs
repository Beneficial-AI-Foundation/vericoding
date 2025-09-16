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
/* helper modified by LLM (iteration 5): prove decode_char_spec yields ASCII uppercase */
proof fn decode_in_bounds(c: int)
    requires
        65 <= c <= 90,
    ensures
        65 <= decode_char_spec(c) <= 90,
{
    assert(decode_char_spec(c) - 65 == (c - 65 + 21) % 26);
    assert(0 <= (c - 65 + 21) % 26);
    assert((c - 65 + 21) % 26 <= 25);
    assert(65 <= decode_char_spec(c));
    assert(decode_char_spec(c) <= 90);
}

/* helper modified by LLM (iteration 5): encode and decode are inverses for uppercase letters */
proof fn encode_decode_inverse(c: int)
    requires
        65 <= c <= 90,
    ensures
        encode_char_spec(decode_char_spec(c)) == c,
{
    assert(decode_char_spec(c) == ((c - 65 + 26 - 5) % 26) + 65);
    assert(encode_char_spec(decode_char_spec(c)) == (((((c - 65 + 26 - 5) % 26) + 65) - 65 + 5) % 26) + 65);
    assert(encode_char_spec(decode_char_spec(c)) == (((c - 65 + 26 - 5) % 26 + 5) % 26) + 65);
    assert(0 <= (c - 65 + 26 - 5) % 26);
    assert((c - 65 + 26 - 5) % 26 <= 25);
    assert(((c - 65 + 26 - 5) % 26 + 5) % 26 == (c - 65) % 26);
    assert(0 <= c - 65);
    assert(c - 65 <= 25);
    assert((c - 65) % 26 == c - 65);
    assert(encode_char_spec(decode_char_spec(c)) == c);
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
/* code modified by LLM (iteration 5): implement decoding using loop with invariants and invoke helpers in proofs */
{
    let mut t: Vec<u8> = Vec::new();
    let mut i: usize = 0;
    while i < s.len()
        invariant
            t.len() == i,
            i <= s.len(),
            forall|k: int| #![auto] 0 <= k < i as int ==> t[k] == decode_char_spec(s[k] as int),
            forall|k: int| #![auto] 0 <= k < i as int ==> encode_char_spec(t[k] as int) == s[k],
        decreases
            s.len() - i
    {
        let c: u8 = s[i];
        let ci: usize = c as usize;
        let decoded_usize: usize = ((ci - 65 + 26 - 5) % 26) + 65;
        let decoded: u8 = decoded_usize as u8;
        t.push(decoded);
        proof {
            let ci_int: int = c as int;
            assert(65 <= ci_int && ci_int <= 90);
            assert(decoded_usize as int == ((ci_int - 65 + 26 - 5) % 26) + 65);
            assert(decoded_usize as int == decode_char_spec(ci_int));
            encode_decode_inverse(ci_int);
            assert(encode_char_spec(decoded_usize as int) == ci_int);
            assert(encode_char_spec(decoded_usize as int) == c as int);
        }
        i = i + 1;
    }
    t
}

// </vc-code>

}
fn main() {}