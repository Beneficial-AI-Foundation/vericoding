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
    /* code modified by LLM (iteration 5): Changed trigger annotations in invariants to match ensures style for better verification */
    let mut result = Vec::<int>::new();
    let mut i = 0;
    while i < lst.len()
        invariant
            result.len() <= i,
            forall|k: int| 0 <= k < result.len() ==> 
                exists|j: int| 0 <= j < i && #[trigger] lst[j] == #[trigger] result[k] && lst[j] != target,
            forall|i1: int, i2: int| 0 <= i1 < i2 < i && lst[i1] != target && lst[i2] != target ==> 
                exists|k1: int, k2: int| 0 <= k1 < k2 < result.len() && 
                #[trigger] lst[i1] == result[k1] && #[trigger] lst[i2] == result[k2],
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