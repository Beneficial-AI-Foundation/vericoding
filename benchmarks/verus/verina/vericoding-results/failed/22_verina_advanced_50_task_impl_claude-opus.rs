// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn is_sorted(v: Seq<nat>) -> bool {
    forall|i: int, j: int| 0 <= i < j < v.len() ==> #[trigger] v[i] <= #[trigger] v[j]
}
// </vc-preamble>

// <vc-helpers>
proof fn merge_sorted_preserves_order(a1: Seq<nat>, a2: Seq<nat>, i1: nat, i2: nat, merged: Seq<nat>)
    requires
        is_sorted(a1),
        is_sorted(a2),
        i1 <= a1.len(),
        i2 <= a2.len(),
        merged.len() == i1 + i2,
        forall|k: int| 0 <= k < i1 ==> exists|j: int| 0 <= j < merged.len() && #[trigger] merged[j] == #[trigger] a1[k],
        forall|k: int| 0 <= k < i2 ==> exists|j: int| 0 <= j < merged.len() && #[trigger] merged[j] == #[trigger] a2[k],
        forall|k: int, l: int| 0 <= k < l < merged.len() ==> #[trigger] merged[k] <= #[trigger] merged[l],
    ensures
        is_sorted(merged)
{
}
// </vc-helpers>

// <vc-spec>
fn merge_sorted(a1: &Vec<nat>, a2: &Vec<nat>) -> (result: Vec<nat>)
    requires 
        is_sorted(a1@),
        is_sorted(a2@),
    ensures
        is_sorted(result@),
        result@.to_multiset() == a1@.to_multiset().add(a2@.to_multiset()),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): added decreases clause to fix loop verification */
    let mut result = Vec::new();
    let mut i1: usize = 0;
    let mut i2: usize = 0;
    
    while i1 < a1.len() || i2 < a2.len()
        invariant
            i1 <= a1.len(),
            i2 <= a2.len(),
            result.len() == i1 + i2,
            is_sorted(result@),
            forall|k: int| 0 <= k < i1 ==> a1@[k] == result@[k] || exists|j: int| i1 <= j < result.len() && result@[j] == a1@[k],
            forall|k: int| 0 <= k < i2 ==> a2@[k] == result@[k] || exists|j: int| i2 <= j < result.len() && result@[j] == a2@[k],
            result@.to_multiset() =~= a1@.subrange(0, i1 as int).to_multiset().add(a2@.subrange(0, i2 as int).to_multiset()),
        decreases a1.len() + a2.len() - i1 - i2
    {
        if i1 >= a1.len() {
            result.push(a2[i2]);
            i2 = i2 + 1;
        } else if i2 >= a2.len() {
            result.push(a1[i1]);
            i1 = i1 + 1;
        } else if a1[i1] <= a2[i2] {
            result.push(a1[i1]);
            i1 = i1 + 1;
        } else {
            result.push(a2[i2]);
            i2 = i2 + 1;
        }
    }
    result
}
// </vc-code>

}
fn main() {}