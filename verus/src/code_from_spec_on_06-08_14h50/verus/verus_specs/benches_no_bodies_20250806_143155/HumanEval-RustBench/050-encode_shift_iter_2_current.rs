use vstd::prelude::*;

verus! {

spec fn encode_char_spec(c: int) -> (result:int)
    recommends
        65 <= c <= 90,
{
    (c - 65 + 5) % 26 + 65
}
// pure-end

fn encode_char(c: u8) -> (r: u8)
    // pre-conditions-start
    requires
        65 <= c <= 90,
    // pre-conditions-end
    // post-conditions-start
    ensures
        r == encode_char_spec(c as int),
        65 <= r <= 90,
    // post-conditions-end
{
    let shifted = (c - 65 + 5) % 26 + 65;
    shifted
}

spec fn decode_char_spec(c: int) -> (result:int)
    recommends
        65 <= c <= 90,
{
    (c - 65 + 26 - 5) % 26 + 65
}
// pure-end

fn decode_char(c: u8) -> (r: u8)
    // pre-conditions-start
    requires
        65 <= c <= 90,
    // pre-conditions-end
    // post-conditions-start
    ensures
        r == decode_char_spec(c as int),
        65 <= r <= 90,
    // post-conditions-end
{
    let shifted = (c - 65 + 21) % 26 + 65;
    shifted
}

proof fn opposite_encode_decode(c: int)
    // pre-conditions-start
    requires
        65 <= c <= 90,
    // pre-conditions-end
    // post-conditions-start
    ensures
        encode_char_spec(decode_char_spec(c)) == c,
        decode_char_spec(encode_char_spec(c)) == c,
    // post-conditions-end
{
    // The proof is automatic due to modular arithmetic properties
    assert(encode_char_spec(decode_char_spec(c)) == 
           ((c - 65 + 26 - 5) % 26 + 65 - 65 + 5) % 26 + 65);
    assert(((c - 65 + 21) % 26 + 5) % 26 + 65 == 
           (c - 65 + 21 + 5) % 26 + 65);
    assert((c - 65 + 26) % 26 + 65 == c - 65 + 65);
    
    assert(decode_char_spec(encode_char_spec(c)) == 
           ((c - 65 + 5) % 26 + 65 - 65 + 21) % 26 + 65);
    assert(((c - 65 + 5) % 26 + 21) % 26 + 65 == 
           (c - 65 + 5 + 21) % 26 + 65);
    assert((c - 65 + 26) % 26 + 65 == c - 65 + 65);
}
// pure-end

#[verifier::loop_isolation(false)]
fn encode_shift(s: &Vec<u8>) -> (t: Vec<u8>)
    // pre-conditions-start
    requires
        forall|i: int| #![trigger s[i]] 0 <= i < s.len() ==> 65 <= s[i] <= 90,
    // pre-conditions-end
    // post-conditions-start
    ensures
        s.len() == t.len(),
        forall|i: int| #![auto] 0 <= i < t.len() ==> t[i] == encode_char_spec(s[i] as int),
        forall|i: int| #![auto] 0 <= i < t.len() ==> decode_char_spec(t[i] as int) == s[i],
    // post-conditions-end
{
    let mut result = Vec::new();
    let mut i = 0;
    
    /* code modified by LLM (iteration 1): added decreases clause for loop termination */
    while i < s.len()
        invariant
            i <= s.len(),
            result.len() == i,
            forall|j: int| #![auto] 0 <= j < i ==> result[j] == encode_char_spec(s[j] as int),
            forall|j: int| #![auto] 0 <= j < i ==> decode_char_spec(result[j] as int) == s[j],
            forall|j: int| #![trigger s[j]] 0 <= j < s.len() ==> 65 <= s[j] <= 90,
        decreases s.len() - i,
    {
        let encoded = encode_char(s[i]);
        result.push(encoded);
        
        proof {
            opposite_encode_decode(s[i as int] as int);
        }
        
        i = i + 1;
    }
    
    result
}

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
{
    let mut result = Vec::new();
    let mut i = 0;
    
    /* code modified by LLM (iteration 1): added decreases clause for loop termination */
    while i < s.len()
        invariant
            i <= s.len(),
            result.len() == i,
            forall|j: int| #![auto] 0 <= j < i ==> result[j] == decode_char_spec(s[j] as int),
            forall|j: int| #![auto] 0 <= j < i ==> encode_char_spec(result[j] as int) == s[j],
            forall|j: int| #![trigger s[j]] 0 <= j < s.len() ==> 65 <= s[j] <= 90,
        decreases s.len() - i,
    {
        let decoded = decode_char(s[i]);
        result.push(decoded);
        
        proof {
            opposite_encode_decode(decoded as int);
        }
        
        i = i + 1;
    }
    
    result
}

}
fn main() {}