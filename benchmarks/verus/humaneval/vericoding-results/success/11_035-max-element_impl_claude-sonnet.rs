// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn max_element(a: &Vec<i32>) -> (max: i32)

    requires
        a.len() > 0,

    ensures
        forall|i: int| 0 <= i < a.len() ==> a[i] <= max,
        exists|i: int| 0 <= i < a.len() && a[i] == max,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): fixed initial invariant by starting loop from index 1 */
    let mut max = a[0];
    let mut idx = 1;
    
    while idx < a.len()
        invariant
            1 <= idx <= a.len(),
            forall|i: int| 0 <= i < idx ==> a[i] <= max,
            exists|i: int| 0 <= i < idx && a[i] == max,
        decreases a.len() - idx,
    {
        if a[idx] > max {
            max = a[idx];
        }
        idx += 1;
    }
    
    max
}
// </vc-code>

}
fn main() {}