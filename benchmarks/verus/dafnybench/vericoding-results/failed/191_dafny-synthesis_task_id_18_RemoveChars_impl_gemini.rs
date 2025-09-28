// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): fixed compilation error by reordering ensures/decreases clauses and removed triggers */
spec fn remove_chars_recursive(s1: Seq<char>, s2: Seq<char>) -> (v: Seq<char>)
    ensures
        v.len() <= s1.len(),
        forall|i: int| 0 <= i < v.len() ==> s1.contains(v[i]) && !s2.contains(v[i]),
        forall|k: int| 0 <= k < s1.len() ==> s2.contains(s1[k]) || v.contains(s1[k]),
    decreases s1.len()
{
    if s1.len() == 0 {
        Seq::empty()
    } else {
        let c = s1.first();
        let rest = s1.subrange(1, s1.len());
        let res_rest = remove_chars_recursive(rest, s2);
        if s2.contains(c) {
            res_rest
        } else {
            seq![c].add(res_rest)
        }
    }
}

// </vc-helpers>

// <vc-spec>
fn remove_chars(s1: Seq<char>, s2: Seq<char>) -> (v: Seq<char>)
    ensures 
        v.len() <= s1.len(),
        forall|i: int| 0 <= i < v.len() ==> s1.contains(v[i]) && !s2.contains(v[i]),
        forall|i: int| 0 <= i < s1.len() ==> s2.contains(s1[i]) || v.contains(s1[i])
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): no changes needed as the fix was in the helper function */
{
    remove_chars_recursive(s1, s2)
}

// </vc-code>

}
fn main() {}