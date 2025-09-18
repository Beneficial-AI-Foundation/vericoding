// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): filter_out removes all occurrences of target while preserving order */
fn filter_out(lst: &Vec<nat>, target: nat) -> (result: Vec<nat>)
    ensures
        forall|i: int| 0 <= i < result.len() ==> #[trigger] result[i] != target,
        forall|i: int| 0 <= i < result.len() ==> 
            exists|j: int| 0 <= j < lst.len() && #[trigger] lst[j] == #[trigger] result[i] && lst[j] != target,
        forall|i: int, j: int| 0 <= i < j < lst.len() && lst[i] != target && lst[j] != target ==> 
            exists|k1: int, k2: int| 0 <= k1 < k2 < result.len() && 
            result[k1] == lst[i] && result[k2] == lst[j],
{
    let mut res: Vec<nat> = Vec::new();
    let mut idx: int = 0 as int;
    while idx < (lst.len() as int)
        invariant
            0 <= idx <= (lst.len() as int),
            forall|p: int| 0 <= p < (res.len() as int) ==> res[p as usize] != target,
            forall|p: int| 0 <= p < (res.len() as int) ==> 
                exists|j: int| 0 <= j < idx && lst[j as usize] == res[p as usize] && lst[j as usize] != target,
            forall|a: int, b: int| 0 <= a < b < idx && lst[a as usize] != target && lst[b as usize] != target ==>
                exists|c1: int, c2: int| 0 <= c1 < c2 < (res.len() as int) && res[c1 as usize] == lst[a as usize] && res[c2 as usize] == lst[b as usize],
        decreases (lst.len() as int) - idx,
    {
        let cur: int = idx;
        if lst[cur as usize] != target {
            res.push(lst[cur as usize]);
        }
        idx = cur + 1;
        proof {
            assert(0 <= idx && idx <= (lst.len() as int));
        }
    }
    let result = res;
    result
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
    /* code modified by LLM (iteration 5): delegate to filter_out helper to compute result */
    let result = filter_out(lst, target);
    result
}

// </vc-code>

}
fn main() {}