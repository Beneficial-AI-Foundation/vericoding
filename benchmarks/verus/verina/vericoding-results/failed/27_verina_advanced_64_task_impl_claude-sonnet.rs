// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Simplified proof body to let Verus handle the automatic proof */
proof fn lemma_push_preserves_order(lst: &Vec<nat>, result: &Vec<nat>, i: int, target: nat, new_elem: nat)
    requires
        0 <= i < lst.len(),
        lst[i as int] == new_elem,
        new_elem != target,
        forall|j1: int, j2: int| 0 <= j1 < j2 < i && lst[j1] != target && lst[j2] != target ==>
            exists|k1: int, k2: int| 0 <= k1 < k2 < result.len() &&
            #[trigger] result[k1] == #[trigger] lst[j1] && #[trigger] result[k2] == #[trigger] lst[j2],
    ensures
        forall|j1: int, j2: int| 0 <= j1 < j2 < i + 1 && lst[j1] != target && lst[j2] != target ==>
            exists|k1: int, k2: int| 0 <= k1 < k2 < result.len() + 1 &&
            (if k1 == result.len() { new_elem } else { #[trigger] result[k1] }) == #[trigger] lst[j1] &&
            (if k2 == result.len() { new_elem } else { #[trigger] result[k2] }) == #[trigger] lst[j2]
{
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
    /* code modified by LLM (iteration 5): Simplified proof blocks and assertions */
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
                #[trigger] result[k1] == #[trigger] lst[j1] && #[trigger] result[k2] == #[trigger] lst[j2],
        decreases lst.len() - i
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