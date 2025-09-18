// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn is_sorted(s: Seq<i32>) -> bool {
    forall|i: int, j: int| 0 <= i < j < s.len() ==> s[i] <= s[j]
}

spec fn multiset_equiv(s1: Seq<i32>, s2: Seq<i32>) -> bool {
    s1.to_multiset() == s2.to_multiset()
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): corrected return name and ensured specs */
spec fn merge_seq(sa: Seq<i32>, sb: Seq<i32>) -> (result: Seq<i32>)
    requires
        is_sorted(sa),
        is_sorted(sb),
    ensures
        is_sorted(result),
        multiset_equiv(result, sa + sb),
    decreases sa.len() + sb.len()
{
    if sa.len() == 0 {
        sb
    } else if sb.len() == 0 {
        sa
    } else {
        let a0 = sa[0];
        let b0 = sb[0];
        if a0 <= b0 {
            seq![a0] + merge_seq(sa[1..], sb)
        } else {
            seq![b0] + merge_seq(sa, sb[1..])
        }
    }
}
// </vc-helpers>

// <vc-spec>
fn merge_sorted(a: Vec<i32>, b: Vec<i32>) -> (result: Vec<i32>)
    requires 
        is_sorted(a@),
        is_sorted(b@),
    ensures 
        is_sorted(result@),
        multiset_equiv(result@, a@ + b@),
// </vc-spec>
// <vc-code>
{
/* code modified by LLM (iteration 5): construct result vec from merged sequence */
    let seq_res = merge_seq(a@, b@);
    let result: Vec<i32> = Vec::from_seq(seq_res);
    result
}
// </vc-code>

}
fn main() {}