// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn argmin(a: Vec<i8>) -> (result: usize)
    requires a.len() > 0,
    ensures
        result < a.len(),
        forall|j: int| 0 <= j < a.len() ==> a[result as int] <= a[j],
        forall|k: int| 0 <= k < result ==> a[k] > a[result as int],
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): added decreases clause to while loop */
    let mut min_idx: usize = 0;
    let mut i: usize = 1;
    
    while i < a.len()
        invariant
            min_idx < a.len(),
            i <= a.len(),
            forall|j: int| 0 <= j < i ==> a[min_idx as int] <= a[j],
            forall|k: int| 0 <= k < min_idx ==> a[k] > a[min_idx as int],
        decreases a.len() - i
    {
        if a[i] < a[min_idx] {
            min_idx = i;
        }
        i += 1;
    }
    
    min_idx
}
// </vc-code>


}
fn main() {}