// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn match_char(c1: u8, c2: u8) -> bool { c1 == c2 || c2 == '?' as u8 }
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
    /* code modified by LLM (iteration 5): fixed invariant syntax by combining invariants into single block */
    let mut i: nat = 0;
    while i < s@.len()
        invariant {
            0 <= i <= s@.len();
            forall|j: int| 0 <= j < i ==> match_char(s@[j], p@[j])
        }
    {
        if !match_char(s@[i], p@[i]) {
            return false;
        }
        i = i + 1;
    }
    true
}
// </vc-code>

}
fn main() {}