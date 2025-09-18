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
/* code modified by LLM (iteration 5): Fixed `nat`/`int` type errors. */
{
    if s.len() == 0 {
        return true;
    }

    let first_char = s.index(0);
    let mut i: nat = 1;

    while i < s.len()
        invariant
            s.len() > 0,
            0 <= i,
            i <= s.len(),
            forall|j: int| 0 <= j < i ==> s.index(j) == first_char,
        decreases (s.len() - i) as int
    {
        if s.index(i) != first_char {
            return false;
        }
        i = i + 1;
    }
    return true;
}
// </vc-code>

}
fn main() {}