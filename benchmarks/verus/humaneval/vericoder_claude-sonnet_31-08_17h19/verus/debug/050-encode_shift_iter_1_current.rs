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
proof fn lemma_decode_char_bounds(c: int)
    requires 65 <= c <= 90
    ensures 65 <= decode_char_spec(c) <= 90
{
    let result = (c - 65 + 26 - 5) % 26 + 65;
    assert((c - 65 + 21) % 26 >= 0);
    assert((c - 65 + 21) % 26 < 26);
}

proof fn lemma_encode_decode_inverse(c: int)
    requires 65 <= c <= 90
    ensures encode_char_spec(decode_char_spec(c)) == c
{
    let decoded = decode_char_spec(c);
    let encoded = encode_char_spec(decoded);
    
    assert(decoded == (c - 65 + 21) % 26 + 65);
    assert(encoded == (decoded - 65 + 5) % 26 + 65);
    assert(encoded == ((c - 65 + 21) % 26 + 5) % 26 + 65);
    assert(encoded == (c - 65 + 26) % 26 + 65);
    assert(encoded == (c - 65) % 26 + 65);
    assert(encoded == c);
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
    let mut result = Vec::new();
    let mut i = 0;
    
    while i < s.len()
        invariant
            0 <= i <= s.len(),
            result.len() == i,
            forall|j: int| #![auto] 0 <= j < i ==> result[j] == decode_char_spec(s[j] as int),
            forall|j: int| #![auto] 0 <= j < i ==> encode_char_spec(result[j] as int) == s[j],
    {
        proof {
            lemma_decode_char_bounds(s[i] as int);
            lemma_encode_decode_inverse(s[i] as int);
        }
        
        let decoded_char = ((s[i] as u8 - 65 + 26 - 5) % 26 + 65) as u8;
        result.push(decoded_char);
        i += 1;
    }
    
    result
}
// </vc-code>

fn main() {}
}