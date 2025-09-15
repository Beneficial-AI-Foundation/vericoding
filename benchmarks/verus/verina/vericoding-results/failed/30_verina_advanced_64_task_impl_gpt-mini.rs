// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): predicate for non-target elements */
spec fn is_non_target(x: nat, t: nat) -> bool { x != t }
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
    /* code modified by LLM (iteration 5): filter out target while preserving order and loop invariants */
    let mut res: Vec<nat> = Vec::new();
    let mut i: int = 0;
    while i < lst.len()
        invariant 0 <= i && i <= lst.len();
        invariant forall |k: int| 0 <= k < res.len() ==> exists |j: int| 0 <= j < i && lst@[j] == res@[k] && lst@[j] != target;
        invariant forall |j: int| 0 <= j < i && lst@[j] != target ==> exists |k: int| 0 <= k < res.len() && res@[k] == lst@[j];
        invariant forall |j1: int, j2: int| 0 <= j1 < j2 < i && lst@[j1] != target && lst@[j2] != target ==> exists |k1: int, k2: int| 0 <= k1 < k2 < res.len() && res@[k1] == lst@[j1] && res@[k2] == lst@[j2];
        decreases lst.len() - i;
    {
        if lst@[i] != target {
            res.push(lst@[i]);
        }
        i = i + 1;
    }
    res
}
// </vc-code>

}
fn main() {}