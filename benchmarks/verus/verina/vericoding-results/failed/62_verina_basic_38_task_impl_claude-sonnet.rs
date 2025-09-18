// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
fn are_all_same_helper(s: Seq<char>, idx: nat) -> (result: bool)
    requires idx <= s.len(),
    ensures
        result ==> (forall|i: int| 0 <= i < idx ==> s@[i] == s@[0]),
        !result ==> (idx > 0 && exists|i: int| 0 <= i < idx && s@[i] != s@[0]),
    decreases s.len() - idx,
{
    /* helper modified by LLM (iteration 5): fix nat literal and sequence indexing */
    if idx == 0nat {
        true
    } else if s@[idx - 1] != s@[0] {
        false
    } else {
        are_all_same_helper(s, idx - 1)
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
    /* code modified by LLM (iteration 5): fix nat literal comparison */
    if s.len() == 0nat {
        true
    } else {
        are_all_same_helper(s, s.len())
    }
}
// </vc-code>

}
fn main() {}