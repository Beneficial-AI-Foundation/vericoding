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
/* code modified by LLM (iteration 5): Fixed type mismatches for indexing into `Vec` by casting loop variable `i` to `usize` for `lst.view_nth()` calls */
{
    let mut result: Vec<nat> = Vec::new();
    let mut i: usize = 0;
    while i < lst.len()
        invariant
            i <= lst.len(),
            forall|k: int| 0 <= k < result.len() ==> #[trigger] result[k] != target,
            forall|k: int| 0 <= k < result.len() ==> exists|j: int| 0 <= j < i as int && #[trigger] lst.view_nth(j as usize) == #[trigger] result[k] && lst.view_nth(j as usize) != target,
            forall|k1: int, k2: int| 0 <= k1 < k2 < result.len() ==> 
                exists|j1: int, j2: int| 
                    0 <= j1 < j2 < i as int
                    && #[trigger] lst.view_nth(j1 as usize) == #[trigger] result[k1]
                    && #[trigger] lst.view_nth(j2 as usize) == #[trigger] result[k2]
                    && lst.view_nth(j1 as usize) != target
                    && lst.view_nth(j2 as usize) != target,
        decreases lst.len() - i
    {
        if lst.view_nth(i) != target { /* changed to view_nth */
            result.push(lst.view_nth(i)); /* changed to view_nth */
        }
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}