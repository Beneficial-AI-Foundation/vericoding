// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

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
    /* code modified by LLM (iteration 5): fixed type mismatches by using int for indexing */
    let mut result = Vec::new();
    let mut i = 0;
    while i < lst.len()
        invariant
            0 <= i <= lst.len(),
            forall|k: int| 0 <= k < result.len() ==> #[trigger] result[k] != target,
            forall|k: int| 0 <= k < result.len() ==> 
                exists|j: int| 0 <= j < i && #[trigger] lst[j] == #[trigger] result[k] && lst[j] != target,
            result.len() == result@.len(),
            forall|p: int| 0 <= p < i && lst[p] != target ==> 
                exists|k: int| 0 <= k < result.len() && result[k] == lst[p],
            forall|p: int, q: int| 0 <= p < q < i && lst[p] != target && lst[q] != target ==> 
                exists|k1: int, k2: int| 0 <= k1 < k2 < result.len() && 
                result[k1] == lst[p] && result[k2] == lst[q],
        decreases lst.len() - i
    {
        if lst[i] != target {
            let old_result_len = result.len() as int;
            result.push(lst[i]);
            assert(result[old_result_len as int] == lst[i as int]);
            assert(forall|k: int| 0 <= k < old_result_len ==> result[k] == result@[k]);
        }
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}