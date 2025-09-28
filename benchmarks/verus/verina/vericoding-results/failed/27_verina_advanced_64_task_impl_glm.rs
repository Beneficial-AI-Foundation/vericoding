// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): fixed indexing and recommends clause */
spec fn count_non_target(lst: &Vec<nat>, target: nat, start: int, end: int) -> nat
    recommends
        0 <= start <= end <= lst.len() as int,
{
    if start >= end {
        0
    } else {
        let c = count_non_target(lst, target, start+1, end);
        if lst[start as usize] != target {
            c + 1
        } else {
            c
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
    /* code modified by LLM (iteration 3): fixed type errors in loop invariant and quantifier */
    let mut result = Vec::new();
    let mut i = 0;
    while i < lst.len()
        invariant
            0 <= i <= lst.len(),
            result.len() == count_non_target(lst, target, 0, i as int),
            forall|k: int| 0 <= k < (i as int) ==> 
                lst[k] != target ==> 
                    exists|idx: int| 0 <= idx < result.len() && result[idx] == lst[k],
            forall|k1: int, k2: int| 
                0 <= k1 < k2 < (i as int) && lst[k1] != target && lst[k2] != target
                ==>
                (count_non_target(lst, target, 0, k1) < count_non_target(lst, target, 0, k2)
                && result[count_non_target(lst, target, 0, k1) as int] == lst[k1]
                && result[count_non_target(lst, target, 0, k2) as int] == lst[k2]),
            forall|idx: int| 0 <= idx < result.len() ==> 
                exists|k: int| 0 <= k < (i as int) && lst[k] != target && result[idx] == lst[k],
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