// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn nanargmax(a: Vec<i8>) -> (idx: usize)
    requires 
        a@.len() > 0,
    ensures 
        idx < a@.len(),
        forall|j: int| 0 <= j < a@.len() ==> a@[j] <= a@[idx as int],
        forall|j: int| 0 <= j < a@.len() && a@[j] == a@[idx as int] ==> (idx as int) <= j,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): Added decreases clause to fix loop verification */
    let mut max_idx: usize = 0;
    let mut max_val: i8 = a[0];
    let mut i: usize = 1;
    
    while i < a.len()
        invariant
            0 <= i <= a@.len(),
            max_idx < i,
            max_idx < a@.len(),
            max_val == a@[max_idx as int],
            forall|j: int| 0 <= j < i ==> a@[j] <= max_val,
            forall|j: int| 0 <= j < i && a@[j] == max_val ==> (max_idx as int) <= j,
        decreases a.len() - i
    {
        if a[i] > max_val {
            max_val = a[i];
            max_idx = i;
        }
        i = i + 1;
    }
    
    max_idx
}
// </vc-code>


}
fn main() {}