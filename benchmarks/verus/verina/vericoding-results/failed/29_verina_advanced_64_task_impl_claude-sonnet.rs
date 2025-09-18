// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): fixed lemma syntax by removing lemma keyword */
fn lemma_order_preserved(lst: &Vec<nat>, target: nat, result: &Vec<nat>, i: int, j: int)
    requires
        0 <= i < j < lst.len(),
        lst[i] != target,
        lst[j] != target,
        forall|k: int| 0 <= k < result.len() ==> result[k] != target,
        forall|k: int| 0 <= k < result.len() ==> 
            exists|m: int| 0 <= m < lst.len() && lst[m] == result[k] && lst[m] != target,
        forall|m1: int, m2: int| 0 <= m1 < m2 < lst.len() && lst[m1] != target && lst[m2] != target ==> 
            exists|k1: int, k2: int| 0 <= k1 < k2 < result.len() && 
            result[k1] == lst[m1] && result[k2] == lst[m2],
    ensures
        exists|k1: int, k2: int| 0 <= k1 < k2 < result.len() && 
        result[k1] == lst[i] && result[k2] == lst[j],
{
    assert(forall|m1: int, m2: int| 0 <= m1 < m2 < lst.len() && lst[m1] != target && lst[m2] != target ==> 
        exists|k1: int, k2: int| 0 <= k1 < k2 < result.len() && 
        result[k1] == lst[m1] && result[k2] == lst[m2]);
}
// </vc-helpers>

// <vc-spec>
fn remove_element(lst: &Vec<nat>, target: nat) -> (result: Vec<nat>)
    ensures
        forall|i: int| 0 <= i < result.len() ==> #[trigger] result[i] != target,
        forall|i: int| 0 <= i < result.len() ==> 
            exists|j: int| 0 <= j < lst.len() && #[trigger] lst[j] == #[trigger] result[i] && lst[j] != target,
        forall|i: int, j: int| 0 <= i < j < lst.len() && lst[i] != target && lst[j] != target ==> 
            exists|k1: int, k2: int| 0 <= k1 < k2 < result.len() && 
            result[k1] == lst[i] && result[k2] == lst[j],
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): simplified implementation with better order preservation tracking */
    let mut result = Vec::new();
    let mut i = 0;
    while i < lst.len()
        invariant
            0 <= i <= lst.len(),
            forall|k: int| 0 <= k < result.len() ==> #[trigger] result[k] != target,
            forall|k: int| 0 <= k < result.len() ==> 
                exists|j: int| 0 <= j < i && #[trigger] lst[j] == #[trigger] result[k] && lst[j] != target,
            forall|j1: int, j2: int| 0 <= j1 < j2 < i && lst[j1] != target && lst[j2] != target ==> 
                exists|k1: int, k2: int| 0 <= k1 < k2 < result.len() && 
                #[trigger] result[k1] == lst[j1] && #[trigger] result[k2] == lst[j2],
        decreases lst.len() - i
    {
        if lst[i] != target {
            result.push(lst[i]);
            proof {
                assert(result[result.len() - 1] == lst[i]);
                assert(lst[i] != target);
            }
        }
        i += 1;
    }
    result
}
// </vc-code>

}
fn main() {}