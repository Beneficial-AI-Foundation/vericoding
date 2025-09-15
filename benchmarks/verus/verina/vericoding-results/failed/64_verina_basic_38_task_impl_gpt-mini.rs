// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): predicate: first n characters equal to s[0] */
spec fn all_pref_equal(s: Seq<char>, n: int) -> bool { forall|i: int| 0 <= i < n ==> s[i] == s[0] }
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
    /* code modified by LLM (iteration 3): return true for empty sequence; otherwise all elements equal to first */
    if s.len() == 0 {
        true
    } else {
        forall|i: int| 0 <= i < s.len() ==> s[i] == s[0]
    }
}
// </vc-code>

}
fn main() {}