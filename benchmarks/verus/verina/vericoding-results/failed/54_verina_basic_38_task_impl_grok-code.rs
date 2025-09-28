// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn all_characters_same_impl(s: Seq<char>) -> bool
{
    /* helper modified by LLM (iteration 5): added nat type annotation for i to fix compilation error */
    if s.len() == 0nat {
        true
    } else {
        let c = s[0];
        let mut i: nat = 1;
        while i < s.len() {
            if s[i] != c {
                return false;
            }
            i = i + 1;
        }
        true
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
    /* code modified by LLM (iteration 5): calls the helper spec function */
    all_characters_same_impl(s)
}
// </vc-code>

}
fn main() {}