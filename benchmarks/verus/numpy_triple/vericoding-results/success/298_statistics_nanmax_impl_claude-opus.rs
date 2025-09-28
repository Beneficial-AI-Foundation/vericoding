// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn nanmax(a: Vec<i8>) -> (result: i8)
    requires a.len() > 0,
    ensures
        /* Case 1: If there exists at least one element, the result is from the vector */
        (exists|max_idx: int| 
            0 <= max_idx < a.len() &&
            result as int == a[max_idx] as int) &&
        /* Case 2: Result is maximum among all elements */
        (forall|j: int| 0 <= j < a.len() ==> a[j] as int <= result as int) &&
        /* Case 3: Result exists in the vector */
        (exists|witness: int| 0 <= witness < a.len() && result as int == a[witness] as int)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): Added decreases clause to while loop */
    let mut max = a[0];
    let mut i = 1;
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            exists|max_idx: int| 0 <= max_idx < i && max == a[max_idx],
            forall|j: int| 0 <= j < i ==> a[j] <= max,
        decreases a.len() - i
    {
        if a[i] > max {
            max = a[i];
        }
        i = i + 1;
    }
    max
}
// </vc-code>


}
fn main() {}