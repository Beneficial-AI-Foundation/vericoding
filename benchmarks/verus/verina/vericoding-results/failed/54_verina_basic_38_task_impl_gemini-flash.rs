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
    /* code modified by LLM (iteration 5): Fixed type mismatches by casting `s.len()` to `int` and carefully handling `nat` to `int` conversions for indexing. */
    if (s.len() as int) <= 1 {
        true
    } else {
        let first_char = s.index(0);
        let mut i: int = 1;
        while i < (s.len() as int)
            invariant
                1 <= i,
                i <= (s.len() as int),
                forall|j: int| 0 <= j < i ==> s.index(j) == first_char,
            decreases (s.len() as int) - i
        {
            if s.index(i) != first_char {
                return false;
            }
            i = i + 1;
        }
        true
    }
}
// </vc-code>

}
fn main() {}