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
    let mut t: Vec<u8> = Vec::new();
    let mut i: int = 0;
    while (i < s.len()) 
    invariant
        t.len() == i &&
        forall |j: int| 0 <= j < t.len() ==> t[j] as int == decode_char_spec(s[j] as int)
    {
        let c = s[i] as int;
        let x = (c - 65 + 21) % 26 + 65;
        assert(65 <= x && x <= 90);
        t.push(x as u8);
        i = i + 1;
    }
    t
}
// </vc-code>

fn main() {}
}