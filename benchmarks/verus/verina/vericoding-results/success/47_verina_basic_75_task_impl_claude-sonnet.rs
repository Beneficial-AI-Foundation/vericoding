// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn min_array(a: &Vec<i32>) -> (result: i32)
    requires a.len() > 0,
    ensures
        forall|i: int| 0 <= i < a.len() ==> result <= a[i],
        exists|i: int| 0 <= i < a.len() && result == a[i],
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): added decreases clause to while loop */
    let mut min_val = a[0];
    let mut idx = 1;
    
    while idx < a.len()
        invariant
            1 <= idx <= a.len(),
            forall|i: int| 0 <= i < idx ==> min_val <= a[i],
            exists|i: int| 0 <= i < idx && min_val == a[i],
        decreases a.len() - idx
    {
        if a[idx] < min_val {
            min_val = a[idx];
        }
        idx += 1;
    }
    
    min_val
}
// </vc-code>

}
fn main() {}