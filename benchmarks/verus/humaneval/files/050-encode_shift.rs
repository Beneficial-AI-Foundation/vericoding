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

#[verifier::loop_isolation(false)]
fn decode_shift(s: &Vec<u8>) -> (t: Vec<u8>)

    requires
        forall|i: int| #![trigger s[i]] 0 <= i < s.len() ==> 65 <= s[i] <= 90,

    ensures
        s.len() == t.len(),
        forall|i: int| #![auto] 0 <= i < t.len() ==> t[i] == decode_char_spec(s[i] as int),
        forall|i: int| #![auto] 0 <= i < t.len() ==> encode_char_spec(t[i] as int) == s[i],
{
    assume(false);
    unreached()
}

}
fn main() {}