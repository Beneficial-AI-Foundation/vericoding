// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): predicate for z/Z characters */
spec fn char_is_z(c: char) -> bool { c == 'z' || c == 'Z' }
// </vc-helpers>

// <vc-spec>
fn contains_z(s: &str) -> (result: bool)
    ensures
        result <==> exists|i: int| 0 <= i < s@.len() && (s@[i] == 'z' || s@[i] == 'Z'),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): imperative search with invariant and post-check */
    let mut i: nat = 0;
    let mut found: bool = false;
    while i < s@.len()
        invariant i <= s@.len()
        invariant found == (exists|j: nat| j < i && char_is_z(s@.index(j)))
    {
        if char_is_z(s@.index(i)) {
            found = true;
        }
        i = i + 1;
    }
    found
}
// </vc-code>

}
fn main() {}