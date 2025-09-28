// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn nanargmin(a: Vec<i8>) -> (result: usize)
    requires 
        a.len() > 0,
    ensures
        result < a.len(),
        forall|j: int| 0 <= j < a@.len() ==> a[result as int] <= a[j],
        forall|j: int| 0 <= j < result ==> a[j] > a[result as int],
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): Added decreases clause to while loop */
    let mut min_idx: usize = 0;
    let mut min_val: i8 = a[0];
    let mut i: usize = 1;
    
    while i < a.len()
        invariant
            0 <= min_idx < a.len(),
            min_idx < i <= a.len(),
            min_val == a[min_idx as int],
            forall|j: int| 0 <= j < i ==> a[min_idx as int] <= a[j],
            forall|j: int| 0 <= j < min_idx ==> a[j] > a[min_idx as int],
        decreases a.len() - i
    {
        if a[i] < min_val {
            min_val = a[i];
            min_idx = i;
        }
        i = i + 1;
    }
    
    min_idx
}
// </vc-code>


}
fn main() {}