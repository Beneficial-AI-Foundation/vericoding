// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): updated comment, no logic change */
proof fn lemma_all_same_from_first(s: Seq<char>)
    requires
        s.len() > 0,
        forall|i: int| 0 <= i < s.len() ==> s@[i] == s@[0],
    ensures
        forall|i: int, j: int| 0 <= i < s.len() && 0 <= j < s.len() ==> s@[i] == s@[j],
{
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
    /* code modified by LLM (iteration 4): Changed loop variable to 'usize' to fix compilation error. */
    if s.len() <= 1 {
        return true;
    }

    let first = s@[0];
    let mut i: usize = 1;
    while i < s.len()
        invariant
            s.len() > 1,
            1 <= i <= s.len(),
            forall|j: int| 0 <= j < i as int ==> s@[j] == first,
    {
        if s@[i] != first {
            return false;
        }
        i = i + 1;
    }

    proof {
        lemma_all_same_from_first(s);
    }
    return true;
}
// </vc-code>

}
fn main() {}