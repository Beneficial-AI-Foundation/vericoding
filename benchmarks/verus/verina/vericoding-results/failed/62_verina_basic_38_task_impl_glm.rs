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
    /* code modified by LLM (iteration 3): fix syntax error in while loop invariants by adding curly braces */
    if s.len() == 0 {
        true
    } else {
        let first_char = s[0];
        let mut all_same = true;
        let mut i = 1;
        while i < s.len()
            invariant { 1 <= i <= s.len() }
            invariant { forall|j: int| 0 <= j < i ==> s[j] == first_char }
            invariant { all_same == (forall|j: int| 0 <= j < i ==> s[j] == first_char) }
        {
            if s[i] != first_char {
                all_same = false;
            }
            i += 1;
        }
        all_same
    }
}
// </vc-code>

}
fn main() {}