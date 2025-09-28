// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn numpy_argmin(a: Vec<i8>) -> (result: usize)
    requires a.len() > 0,
    ensures 
        result < a.len(),
        forall|j: int| 0 <= j < a@.len() ==> a@[result as int] <= a@[j],
        forall|j: int| 0 <= j < a@.len() && a@[j] == a@[result as int] ==> (result as int) <= j,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): fixed invariant to handle case where equal elements are found after current min_idx */
    let mut min_idx: usize = 0;
    let mut i: usize = 1;
    
    while i < a.len()
        invariant
            0 <= min_idx < a.len(),
            1 <= i <= a.len(),
            forall|j: int| 0 <= j < i ==> a@[min_idx as int] <= a@[j],
            forall|j: int| 0 <= j < min_idx ==> a@[min_idx as int] < a@[j] || (min_idx as int) <= j,
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