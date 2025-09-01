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
proof fn lemma_encode_decode_inverse(c: int)
    requires
        65 <= c <= 90,
    ensures
        encode_char_spec(decode_char_spec(c)) == c,
{
    // decode_char_spec(c) = (c - 65 + 26 - 5) % 26 + 65 = (c - 65 + 21) % 26 + 65
    // encode_char_spec(decode_char_spec(c)) = ((c - 65 + 21) % 26 + 65 - 65 + 5) % 26 + 65
    //                                        = ((c - 65 + 21) % 26 + 5) % 26 + 65
    
    let shifted = (c - 65 + 21) % 26;
    assert(0 <= shifted < 26);
    
    // We need to show that (shifted + 5) % 26 == c - 65
    // shifted = (c - 65 + 21) % 26
    
    if c - 65 + 21 < 26 {
        assert(shifted == c - 65 + 21);
        assert((shifted + 5) % 26 == (c - 65 + 21 + 5) % 26);
        assert((c - 65 + 21 + 5) == c - 65 + 26);
        assert((c - 65 + 26) % 26 == c - 65);
    } else {
        assert(c - 65 + 21 >= 26);
        assert(c - 65 >= 5);
        assert(shifted == c - 65 + 21 - 26);
        assert(shifted == c - 65 - 5);
        assert((shifted + 5) % 26 == (c - 65 - 5 + 5) % 26);
        assert((c - 65) % 26 == c - 65);
    }
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
    let mut t = Vec::new();
    let mut i: usize = 0;
    
    while i < s.len()
        invariant
            i <= s.len(),
            t.len() == i,
            forall|j: int| #![trigger s[j]] 0 <= j < s.len() ==> 65 <= s[j] <= 90,
            forall|j: int| #![auto] 0 <= j < i ==> t[j] == decode_char_spec(s[j] as int),
            forall|j: int| #![auto] 0 <= j < i ==> encode_char_spec(t[j] as int) == s[j],
        decreases s.len() - i,
    {
        let c = s[i];
        assert(65 <= c <= 90);
        
        let decoded = ((c - 65 + 26 - 5) % 26 + 65) as u8;
        
        assert(decoded == decode_char_spec(c as int));
        
        proof {
            lemma_encode_decode_inverse(c as int);
            assert(encode_char_spec(decoded as int) == c);
        }
        
        t.push(decoded);
        i = i + 1;
    }
    
    t
}
// </vc-code>

fn main() {}
}