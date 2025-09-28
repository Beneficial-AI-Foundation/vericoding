// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): spec helper that checks all elements equal to the first */
spec fn seq_all_equal_to_first(s: Seq<char>) -> bool {
    if s.len() == 0 {
        true
    } else {
        forall|i: int, j: int| 0 <= i < s.len() && 0 <= j < s.len() ==> s[i] == s[j]
    }
}
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
    /* code modified by LLM (iteration 5): determine if all characters in seq are equal */
    if s.len() == 0 {
        true
    } else {
        forall|i: int, j: int| 0 <= i < s.len() && 0 <= j < s.len() ==> s[i] == s[j]
    }
}
// </vc-code>

}
fn main() {}