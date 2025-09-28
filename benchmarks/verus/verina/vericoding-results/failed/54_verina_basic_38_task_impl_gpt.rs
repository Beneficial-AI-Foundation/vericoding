// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): fix nat/int mismatch and use Seq.index in spec context */
spec fn all_chars_same_spec(s: Seq<char>) -> bool {
    s.len() == 0nat || (forall|i: int| 0 <= i && i < s.len() ==> s.index(i) == s.index(0))
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
    /* code modified by LLM (iteration 5): compute property using Seq.index and correct nat literal */
    s.len() == 0nat || (forall|i: int| 0 <= i && i < s.len() ==> s.index(i) == s.index(0))
}
// </vc-code>

}
fn main() {}