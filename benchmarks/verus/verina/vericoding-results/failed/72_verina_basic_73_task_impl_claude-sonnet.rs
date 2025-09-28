// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): fix type mismatch - s@ returns Seq<char>, use as_bytes() for Seq<u8> */
spec fn str_bytes(s: &str) -> Seq<u8>
{
    s.as_bytes()@
}

spec fn byte_at(s: &str, i: int) -> u8
    requires 0 <= i < s.as_bytes()@.len()
{
    s.as_bytes()@.index(i)
}
// </vc-helpers>

// <vc-spec>
fn match_strings(s: &str, p: &str) -> (result: bool)
    requires s@.len() == p@.len(),
    ensures
        result == (forall|n: int| 0 <= n < s@.len() ==> 
            (s@.index(n) == p@.index(n) || p@.index(n) == '?' as u8)),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fix spec by using as_bytes() in postcondition */
    let mut i = 0;
    while i < s.len()
        invariant
            0 <= i <= s.as_bytes()@.len(),
            s.as_bytes()@.len() == p.as_bytes()@.len(),
            forall|n: int| 0 <= n < i ==> (s.as_bytes()@.index(n) == p.as_bytes()@.index(n) || p.as_bytes()@.index(n) == '?' as u8),
    {
        proof {
            assert(0 <= i < s.as_bytes()@.len());
            assert(0 <= i < p.as_bytes()@.len());
        }
        if s.as_bytes()[i] != p.as_bytes()[i] && p.as_bytes()[i] != '?' as u8 {
            return false;
        }
        i += 1;
    }
    true
}
// </vc-code>

}
fn main() {}