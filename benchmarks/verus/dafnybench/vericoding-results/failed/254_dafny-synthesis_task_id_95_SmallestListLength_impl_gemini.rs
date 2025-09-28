// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn min(a: int, b: int) -> int {
    if a < b { a } else { b }
}

/* helper modified by LLM (iteration 5): named the return value in the spec function signature */
spec fn smallest_len_recursive(s: Seq<Seq<int>>, i: int) -> (result: int)
    requires
        0 <= i < s.len(),
    ensures
        forall|j: int| i <= j < s.len() ==> result <= s[j].len(),
        exists|k: int| i <= k < s.len() && result == #[trigger] s[k].len(),
    decreases s.len() - i,
{
    if i == s.len() - 1 {
        s[i].len()
    } else {
        let rest_min = smallest_len_recursive(s, i + 1);
        min(s[i].len(), rest_min)
    }
}
// </vc-helpers>

// <vc-spec>
fn smallest_list_length(s: Seq<Seq<int>>) -> (v: int)
    requires
        s.len() > 0,
    ensures
        forall|i: int| 0 <= i < s.len() ==> v <= s[i].len(),
        exists|i: int| 0 <= i < s.len() && v == #[trigger] s[i].len(),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fixed helper function signature, logic unchanged */
    smallest_len_recursive(s, 0)
}
// </vc-code>

}
fn main() {}