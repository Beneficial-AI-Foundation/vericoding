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
/* helper modified by LLM (iteration 4): removed requires/ensures from spec function */
spec fn decode_char_in_range(c: int) -> bool
{
    65 <= c <= 90 && 65 <= decode_char_spec(c) <= 90
}

proof fn prove_decode_char_in_range(c: int)
    requires 65 <= c <= 90
    ensures decode_char_in_range(c)
{
    let decoded = (c - 65 + 26 - 5) % 26 + 65;
    assert(0 <= (c - 65 + 26 - 5) % 26 <= 25);
    assert(65 <= decoded <= 90);
}

proof fn encode_decode_inverse(c: int)
    requires 65 <= c <= 90
    ensures encode_char_spec(decode_char_spec(c)) == c
{
    let decoded = decode_char_spec(c);
    let base_c = c - 65;
    let shifted_back = (base_c + 26 - 5) % 26;
    let encoded_back = (shifted_back + 5) % 26;
    assert((base_c + 26 - 5 + 5) % 26 == (base_c + 26) % 26);
    assert((base_c + 26) % 26 == base_c);
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
    /* code modified by LLM (iteration 4): added decreases clause to while loop */
    let mut result = Vec::new();
    let mut i = 0;
    
    while i < s.len()
        invariant
            0 <= i <= s.len(),
            result.len() == i,
            forall|j: int| #![auto] 0 <= j < i ==> result[j] == decode_char_spec(s[j] as int),
            forall|j: int| #![auto] 0 <= j < i ==> encode_char_spec(result[j] as int) == s[j],
        decreases s.len() - i
    {
        let c = s[i];
        proof {
            prove_decode_char_in_range(c as int);
        }
        
        let shift_val = (c - 65 + 21) % 26;
        let decoded = shift_val + 65;
        result.push(decoded);
        
        proof {
            encode_decode_inverse(c as int);
        }
        
        i += 1;
    }
    
    result
}
// </vc-code>

}
fn main() {}