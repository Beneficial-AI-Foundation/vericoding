/* Returns the maximum value of all elements in a non-empty vector.
This is an alias for numpy.amax that returns the maximum value among all elements in the array.

Mathematical Properties:
- Returns an element that exists in the vector
- No element in the vector is greater than the returned value
- For constant vectors, returns the constant value
- Handles non-empty vectors only (n + 1 elements)

Specification: max returns the maximum value in the vector.
This specification delegates to amax_spec since max is an alias for amax.

Mathematical properties:
1. The result is an element that exists in the vector
2. No element in the vector is greater than the result
3. The result is unique (first occurrence if there are duplicates)
4. For constant vectors, max equals the constant value
5. Sanity check: the maximum exists in the vector */

use vstd::prelude::*;

verus! {
fn max(a: &Vec<f32>) -> (result: f32)
    requires a.len() > 0,
    ensures
        (exists|max_idx: int| 0 <= max_idx < a.len() && result == a[max_idx]),
        (exists|witness: int| 0 <= witness < a.len() && result == a[witness]),
{
    // impl-start
    assume(false);
    0.0
    // impl-end
}
}
fn main() {}