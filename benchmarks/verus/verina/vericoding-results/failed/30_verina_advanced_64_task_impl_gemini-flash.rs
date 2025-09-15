// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Removed unnecessary helper definitions to simplify the code. */
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
/* code modified by LLM (iteration 5): Fixed type casting issues for 'int' and 'nat' indices to resolve compilation errors. */
{
    let mut result: Vec<nat> = Vec::new();
    let mut i: usize = 0;

    while i < lst.len()
        invariant
            i <= lst.len(),
            forall|j: int| 0 <= j < result.len() ==> #[trigger] result[j] != target,
            forall|j: int| 0 <= j < result.len() ==> 
                exists|k: int| 0 <= k < i as int && #[trigger] lst.view()@[k] == #[trigger] result[j] && lst.view()@[k] != target,
            forall|k1: int, k2: int| 0 <= k1 < k2 < result.len() ==> 
                exists|idx1: int, idx2: int| 0 <= idx1 < idx2 < i as int && 
                lst.view()@[idx1] != target && lst.view()@[idx2] != target &&
                result[k1] == lst.view()@[idx1] && result[k2] == lst.view()@[idx2]
    {
        if lst.view()@[i as int] != target {
            result.push(lst.view()@[i as int]);
        }
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}