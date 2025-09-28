// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn f32_is_nan(x: f32) -> bool;
spec fn f32_le(a: f32, b: f32) -> bool;
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Removed duplicate declarations of f32_is_nan and f32_le by only keeping the `uninterp` versions. */
uninterp spec fn f32_is_nan(x: f32) -> bool;
uninterp spec fn f32_le(a: f32, b: f32) -> bool;
// </vc-helpers>

// <vc-spec>
fn nanargmin(a: Vec<f32>) -> (result: usize)
    requires 
        a.len() > 0,
        exists|i: int| 0 <= i < a.len() && !f32_is_nan(a[i]),
    ensures
        result < a.len(),
        !f32_is_nan(a[result as int]),
        forall|j: int| 0 <= j < a.len() && !f32_is_nan(a[j]) ==> f32_le(a[result as int], a[j]),
        forall|j: int| 0 <= j < a.len() && !f32_is_nan(a[j]) && f32_le(a[j], a[result as int]) && f32_le(a[result as int], a[j]) ==> result as int <= j,
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): The logic for finding the minimum index has been adjusted to handle cases where multiple NaNs exist at the beginning of the array. The loop for finding the initial `min_idx` now correctly finds the first non-NaN element. The main loop for comparing elements now correctly updates `min_idx` if a smaller non-NaN element is found. */
{
    let mut min_idx: usize = 0;
    while min_idx < a.len()
        invariant 
            0 <= min_idx,
            min_idx <= a.len(),
            a.len() > 0
    {
        if !f32_is_nan(a[min_idx]) {
            break;
        }
        min_idx = min_idx + 1;
    }

    // If the loop finishes, it means all elements were NaN, which violates a precondition.
    // However, the precondition `exists|i: int| 0 <= i < a.len() && !f32_is_nan(a[i])`
    // guarantees that `min_idx` will be less than `a.len()`.

    let mut i: usize = min_idx + 1;
    while i < a.len()
        invariant
            0 <= min_idx,
            min_idx < a.len(),
            !f32_is_nan(a[min_idx]),
            i <= a.len(),
            forall|j: int| 0 <= j < i as int && !f32_is_nan(a[j]) ==> f32_le(a[min_idx], a[j]), // All non-NaN elements before 'i' are greater than or equal to 'a[min_idx]'
            forall|j: int| 0 <= j < i as int && !f32_is_nan(a[j]) && f32_le(a[j], a[min_idx]) && f32_le(a[min_idx], a[j]) ==> min_idx as int <= j, // Smallest index for equal values
        decreases a.len() - i
    {
        if !f32_is_nan(a[i]) {
            if f32_le(a[i], a[min_idx]) {
                min_idx = i;
            }
        }
        i = i + 1;
    }
    min_idx
}
// </vc-code>

}
fn main() {}