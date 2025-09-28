// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn all_equal_up_to(s: Seq<char>, first: char, i: int) -> bool {
    forall|j: int| 0 <= j < i ==> s[j] == first
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
    if s.len() == 0 {
        true
    } else {
        let first = s[0];
        let mut all_same = true;
        let mut i = 1;
        while i < s.len()
            invariant
                1 <= i <= s.len(),
                all_same == all_equal_up_to(s, first, i),
            decreases s.len() - i,
        {
            if s[i] != first {
                all_same = false;
                break;
            }
            i += 1;
        }
        all_same
    }
}
// </vc-code>

}
fn main() {}