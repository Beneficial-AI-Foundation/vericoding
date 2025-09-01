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
proof fn lemma_decode_formula(c: int)
    requires 65 <= c <= 90
    ensures decode_char_spec(c) == (c - 65 + 21) % 26 + 65
{
    assert(decode_char_spec(c) == (c - 65 + 21) % 26 + 65);
}

proof fn lemma_round_trip(c: int)
    requires 65 <= c <= 90
    ensures encode_char_spec(decode_char_spec(c)) == c
{
    let x = c - 65;
    assert(0 <= x <= 25);
    let decoded = decode_char_spec(c);
    assert(decoded == (x + 21) % 26 + 65);
    let encoded = encode_char_spec(decoded);
    assert(encoded == ( ( (x+21) % 26 ) + 5 ) % 26 + 65);
    if x < 5 {
        assert((x+21) % 26 == x+21);
        assert( (x+21+5) % 26 == (x+26) % 26 );
        assert( (x+26) % 26 == x );
    } else {
        assert((x+21) % 26 == x+21-26);
        assert( (x+21-26+5) % 26 == (x) % 26 );
        assert( x % 26 == x );
    }
    assert(encoded == x + 65);
    assert(x+65 == c);
}
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
    let mut t = Vec::with_capacity(s.len());
    for i in 0..s.len()
        invariant
            t.len() == i,
            forall|j: int| 0 <= j < i ==> t[j] == decode_char_spec(s[j] as int),
            forall|j: int| 0 <= j < i ==> encode_char_spec(t[j] as int) == s[j],
    {
        let c = s[i];
        let c_int = c as int;
        lemma_decode_formula(c_int);
        let decoded = (c_int - 65 + 21) % 26 + 65;
        lemma_round_trip(c_int);
        t.push(decoded as u8);
    }
    t
}
// </vc-code>

fn main() {}
}