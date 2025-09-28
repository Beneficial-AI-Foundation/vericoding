// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
proof fn remove_element_helper(lst: Seq<nat>, target: nat, idx: int) -> (result: Seq<nat>)
    requires
        0 <= idx <= lst.len(),
    ensures
        result == lst.filter(|v: nat| v != target),
        forall|i: int| 0 <= i < result.len() ==> #[trigger] result[i] != target,
        forall|i: int| 0 <= i < result.len() ==> 
            exists|j: int| 0 <= j < lst.len() && #[trigger] lst[j] == #[trigger] result[i] && lst[j] != target,
        forall|i: int, j: int| 0 <= i < j < lst.len() && lst[i] != target && lst[j] != target ==> 
            exists|k1: int, k2: int| 0 <= k1 < k2 < result.len() && 
            result[k1] == lst[i] && result[k2] == lst[j],
    decreases lst.len() - idx,
{
    if idx == lst.len() {
        Seq::empty()
    } else {
        let rest = remove_element_helper(lst, target, idx + 1);
        if lst[idx] == target {
            rest
        } else {
            rest.insert(0, lst[idx])
        }
    }
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
    /* code modified by LLM (iteration 5): Fixed while loop invariants to maintain proper ordering */
    let mut result = Vec::new();
    let mut i: usize = 0;
    
    while i < lst.len()
        invariant
            i <= lst.len(),
            forall|k: int| 0 <= k < result.len() ==> #[trigger] result[k] != target,
            forall|k: int| 0 <= k < result.len() ==> 
                exists|j: int| 0 <= j < i && #[trigger] lst[j] == #[trigger] result[k] && lst[j] != target,
            forall|k: int, l: int| 0 <= k < l < i && lst[k] != target && lst[l] != target ==> 
                exists|m1: int, m2: int| 0 <= m1 < m2 < result.len() && 
                result[m1] == lst[k] && result[m2] == lst[l],
        decreases lst.len() - i,
    {
        if lst[i] != target {
            result.push(lst[i]);
        }
        i += 1;
    }
    result
}
// </vc-code>

}
fn main() {}