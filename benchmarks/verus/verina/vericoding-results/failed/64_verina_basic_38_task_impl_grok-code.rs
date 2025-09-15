// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn all_characters_same(s: Seq<char>) -> (result: bool)
    requires true,
    ensures
        result ==> (forall|i: int, j: int| 0 <= i < s.len() && 0 <= j < s.len() ==> s[i] == s[j]),
        !result ==> (s.len() > 0 && exists|i: int| 0 <= i < s.len() && #[trigger] s[i] != s[0]),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Fixed compilation error by moving the invariants inside the loop body and adding decreases clause for termination. */
    if s.len() == 0 {
        return true;
    }
    let first = s@[0];
    let mut i = 1;
    while i < s.len() {
        invariant i <= s.len()
        invariant forall |k: int| 0 <= k < i ==> #[trigger] s[k] == s[0]
        decreases s.len() - i
        if s@[i] != first {
            return false;
        }
        i = i + 1;
    }
    return true;
}
// </vc-code>

}
fn main() {}