// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): removed recursion and decreases clause */
spec fn count_non_target(lst: &Vec<nat>, target: nat, end: int) -> nat
{
    if end <= 0 {
        0nat
    } else {
        let mut count = 0nat;
        let mut j = 0;
        while j < end {
            if lst[j] != target {
                count = count + 1;
            }
            j = j + 1;
        }
        count
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
/* code modified by LLM (iteration 5): added decreases clause to while loop */
{
    let mut result = Vec::new();
    let mut i = 0;
    
    while i < lst.len()
        invariant
            0 <= i <= lst.len(),
            forall|j: int| 0 <= j < result.len() ==> result[j] != target,
            forall|j: int| 0 <= j < result.len() ==> 
                exists|k: int| 0 <= k < i && lst[k] == result[j] && lst[k] != target,
            forall|j1: int, j2: int| 0 <= j1 < j2 < i && lst[j1] != target && lst[j2] != target ==> 
                exists|k1: int, k2: int| 0 <= k1 < k2 < result.len() && 
                result[k1] == lst[j1] && result[k2] == lst[j2]
        decreases lst.len() - i
    {
        if lst[i] != target {
            result.push(lst[i]);
        }
        i = i + 1;
    }
    
    result
}
// </vc-code>

}
fn main() {}