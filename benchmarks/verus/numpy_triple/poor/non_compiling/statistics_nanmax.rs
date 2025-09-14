/* Returns the maximum value of all elements in a non-empty vector, ignoring NaN values.
When all elements are NaN, returns NaN.

Mathematical Properties:
- Ignores NaN values in the computation
- Returns the maximum of all non-NaN elements
- If all elements are NaN, returns NaN
- If at least one element is not NaN, returns the maximum non-NaN value
- For vectors with no NaN values, behaves identically to regular max

Specification: nanmax returns the maximum value in the vector, ignoring NaN values.

Mathematical properties:
1. If there exists at least one non-NaN element, the result is the maximum among non-NaN elements
2. If all elements are NaN, the result is NaN
3. The result is either a non-NaN element from the vector or NaN
4. For vectors without NaN values, nanmax behaves identically to regular max
5. NaN values are completely ignored during the maximum computation
6. Sanity check: result is either NaN or exists in the vector */

use vstd::prelude::*;

verus! {
fn nanmax(a: Vec<f32>) -> (result: f32)
    requires a.len() > 0,
    ensures
        /* Case 1: If there exists at least one non-NaN element */
        (exists|i: int| 0 <= i < a.len() && !result.is_nan() && !a[i].is_nan()) ==>
            (exists|max_idx: int| 0 <= max_idx < a.len() &&
                result == a[max_idx] &&
                !a[max_idx].is_nan() &&
                (forall|j: int| 0 <= j < a.len() && !a[j].is_nan() ==> a[j] <= result)),
        /* Case 2: If all elements are NaN, result is NaN */
        (forall|i: int| 0 <= i < a.len() ==> a[i].is_nan()) ==> result.is_nan(),
        /* Case 3: NaN values are ignored (result is max of non-NaN elements) */
        !result.is_nan() ==>
            (exists|witness: int| 0 <= witness < a.len() &&
                result == a[witness] &&
                !a[witness].is_nan() &&
                (forall|j: int| 0 <= j < a.len() && !a[j].is_nan() ==> a[j] <= result)),
        /* Case 4: For vectors without NaN, behaves like regular max */
        (forall|i: int| 0 <= i < a.len() ==> !a[i].is_nan()) ==>
            (exists|max_idx: int| 0 <= max_idx < a.len() &&
                result == a[max_idx] &&
                (forall|j: int| 0 <= j < a.len() ==> a[j] <= result)),
        /* Sanity check: result is either NaN or exists in the vector */
        result.is_nan() || (exists|witness: int| 0 <= witness < a.len() && result == a[witness])
{
    // impl-start
    assume(false);
    0.0
    // impl-end
}
}
fn main() {}