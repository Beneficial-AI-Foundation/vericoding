// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn chars_match_at(s: Seq<u8>, p: Seq<u8>, i: int) -> bool
    recommends 0 <= i < s.len() && i < p.len()
{
    s.index(i) == p.index(i) || p.index(i) == '?' as u8
}

proof fn chars_match_lemma(s: Seq<u8>, p: Seq<u8>, i: usize)
    requires 0 <= i < s.len() && i < p.len()
    ensures chars_match_at(s, p, i as int) == (s.index(i as int) == p.index(i as int) || p.index(i as int) == '?' as u8)
{
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
    let mut i = 0;
    while i < s.len()
        invariant
            0 <= i <= s.len(),
            s@.len() == p@.len(),
            forall|n: int| 0 <= n < i ==> (s@.index(n) == p@.index(n) || p@.index(n) == '?' as u8),
    {
        if s.as_bytes()[i] != p.as_bytes()[i] && p.as_bytes()[i] != b'?' {
            return false;
        }
        i += 1;
    }
    true
}
// </vc-code>

}
fn main() {}