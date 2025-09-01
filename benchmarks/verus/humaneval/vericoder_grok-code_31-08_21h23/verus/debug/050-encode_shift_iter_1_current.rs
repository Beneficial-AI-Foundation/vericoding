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
    for i in 0..s.len()
        invariant
            t.len() == i,
            forall|j: int| 0 <= j < i ==> t[j] as int == decode_char_spec(s[j] as int),
            forall|j: int| 0 <= j < i ==> encode_char_spec(t[j] as int) == s[j] as int
    {
        let orig = s[i] as int;
        let decoded_num = ((orig - 65) + (26 - 5)) % 26 + 65;
        proof {
            assert(decoded_num == decode_char_spec(orig));
            assert(encode_char_spec(decoded_num) == orig);
        }
        t.push(decoded_num as u8);
    }
    t
}
// </vc-code>

fn main() {}
}