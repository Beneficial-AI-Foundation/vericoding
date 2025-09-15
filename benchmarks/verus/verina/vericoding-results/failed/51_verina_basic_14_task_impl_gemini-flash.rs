// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): The helper section was empty in original, still empty as no helpers are truly needed for this problem. */
// </vc-helpers>

// <vc-spec>
fn contains_z(s: &str) -> (result: bool)
    ensures
        result <==> exists|i: int| 0 <= i < s@.len() && (s@[i] == 'z' || s@[i] == 'Z'),
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Fixed compilation error by removing the `as nat` cast within the `while` loop condition as `i` is already `nat`. */
{
    let s_seq = s@;
    let mut i: nat = 0;
    while i < s_seq.len()
        invariant
            0 <= i as int <= s_seq.len() as int,
            forall|j: int| 0 <= j < i ==> (s_seq@[j] != 'z' && s_seq@[j] != 'Z'),
    {
        if s_seq@[i] == 'z' || s_seq@[i] == 'Z' {
            return true;
        }
        i = i + 1;
    }
    false
}
// </vc-code>

}
fn main() {}