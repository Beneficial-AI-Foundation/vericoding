// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): No helpers are needed for nanmax. */

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
/* code modified by LLM (iteration 4): Added a `decreases` clause to the while loop which was the cause of the verification error. */
{
    let mut max_val = a[0];
    let mut i = 1;

    while i < a.len()
        invariant
            0 < i as int <= a.len() as int,
            exists|k: int| 0 <= k < i as int && max_val as int == a[k as int] as int,
            forall|j: int| 0 <= j < i as int ==> a[j as int] as int <= max_val as int,
        decreases a.len() - i
    {
        if a[i] > max_val {
            max_val = a[i];
        }
        i = i + 1;
    }
    max_val
}
// </vc-code>


}
fn main() {}