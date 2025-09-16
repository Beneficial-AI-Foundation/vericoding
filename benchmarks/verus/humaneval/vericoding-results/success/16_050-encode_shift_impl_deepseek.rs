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
/* helper modified by LLM (iteration 4): Fixed ghost function return value with explicit return */
proof fn decode_char_ghost(c: u8) -> (decoded: u8)
    requires
        65 <= c <= 90,
    ensures
        decoded == decode_char_spec(c as int) as u8,
{
    let c_int = c as int;
    assert(65 <= c_int <= 90);
    let shifted = c_int - 65 + 26 - 5;
    let modulo_result = shifted % 26;
    let final_result = modulo_result + 65;
    assert(final_result == decode_char_spec(c_int));
    (final_result as u8)
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
/* code modified by LLM (iteration 4): Maintained implementation with proper ghost function call */
{
    let mut t = Vec::new();
    let mut i: usize = 0;
    
    while i < s.len()
        invariant
            i <= s.len(),
            t.len() == i,
            forall|j: int| 0 <= j < i ==> t[j] == decode_char_spec(s[j] as int),
            forall|j: int| 0 <= j < i ==> encode_char_spec(t[j] as int) == s[j],
        decreases s.len() - i,
    {
        let c = s[i];
        proof {
            decode_char_ghost(c);
        }
        let decoded = ((c as u16 - 65 + 26 - 5) % 26 + 65) as u8;
        t.push(decoded);
        i += 1;
    }
    t
}
// </vc-code>

}
fn main() {}