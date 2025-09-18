// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn nanmax(a: Vec<i32>) -> (result: i32)
    requires a.len() > 0,
    ensures
        /* Case 1: If there exists at least one element, the result is from the vector */
        (exists|max_idx: int| 
            0 <= max_idx < a.len() &&
            result == a[max_idx]) &&
        /* Case 2: Result is maximum among all elements */
        (forall|j: int| 0 <= j < a.len() ==> a[j] <= result) &&
        /* Case 3: Result exists in the vector */
        (exists|witness: int| 0 <= witness < a.len() && result == a[witness])
// </vc-spec>
// <vc-code>
{
    // impl-start
    assume(false);
    unreached()
    // impl-end
}
// </vc-code>


}
fn main() {}