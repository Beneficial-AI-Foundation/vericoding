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
    /* code modified by LLM (iteration 5): Add decreases clause to fix compilation error. */
    let mut result: Vec<nat> = Vec::new();
    let mut i: usize = 0;
    while i < lst.len()
        decreases lst.len() - i
        invariant
            0 <= i <= lst.len(),
            forall|k: int| 0 <= k < result@.len() ==> #[trigger] result@[k] != target,
            forall|k: int| 0 <= k < result@.len() ==> 
                exists|j: int| 0 <= j < (i as int) && #[trigger] lst@[j] == #[trigger] result@[k] && lst@[j] != target,
            forall|k1: int, k2: int| 0 <= k1 < k2 < result@.len() ==> 
                exists|j1: int, j2: int| 0 <= j1 < j2 < (i as int) && 
                lst@[j1] == result@[k1] && lst@[j2] == result@[k2],
    {
        if lst[i] != target {
            result.push(lst[i]);
            proof {
                assert(result@[result@.len() as int - 1] != target);
                assert(exists|j: int| j == (i as int) && #[trigger] lst@[j] == #[trigger] result@[result@.len() as int - 1] && lst@[j] != target);
            }
        }
        i += 1;
    }
    proof {
        // Prove the postconditions
        assert(forall|i: int| 0 <= i < result@.len() ==> #[trigger] result@[i] != target);
        assert(forall|i: int| 0 <= i < result@.len() ==> 
            exists|j: int| 0 <= j < lst@.len() && #[trigger] lst@[j] == #[trigger] result@[i] && lst@[j] != target);
        assert(forall|i: int, j: int| 0 <= i < j < lst@.len() && lst@[i] != target && lst@[j] != target ==> 
            exists|k1: int, k2: int| 0 <= k1 < k2 < result@.len() && 
            result@[k1] == lst@[i] && result@[k2] == lst@[j]);
    }
    result
}
// </vc-code>

}
fn main() {}