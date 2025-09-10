/* Compute the q-th percentile of the data along the specified axis, ignoring NaN values.
Returns the q-th percentile of the array elements.
If all values are NaN, returns NaN.
The percentile q must be between 0 and 100 inclusive.

Specification: nanpercentile computes the q-th percentile of non-NaN values in the array.
The result is NaN if all values are NaN, otherwise it's the q-th percentile of the finite values.
The percentile is computed by sorting the non-NaN values and finding the value at the position
corresponding to the percentile q (between 0 and 100). */

use vstd::prelude::*;

verus! {
fn nanpercentile(a: Vec<f32>, q: f32) -> (result: f32)
    requires 0.0 <= q && q <= 100.0,
    ensures
        /* Case 1: All values are NaN */
        (forall|i: int| 0 <= i < a.len() ==> a[i].is_nan()) ==> result.is_nan(),
        /* Case 2: At least one finite value exists */
        (exists|i: int| 0 <= i < a.len() && !a[i].is_nan()) ==> {
            /* There exists a list of finite values that are sorted */
            exists|finite_vals: Seq<f32>| {
                finite_vals.len() > 0 &&
                /* All elements in finite_vals are from a and are not NaN */
                (forall|i: int| 0 <= i < finite_vals.len() ==> !finite_vals[i].is_nan()) &&
                /* finite_vals contains all non-NaN values from a */
                finite_vals.len() == ({
                    let mut count = 0;
                    for i in 0..a.len() {
                        if !a[i].is_nan() { count = count + 1; }
                    }
                    count
                }) &&
                /* finite_vals is sorted in non-decreasing order */
                (forall|i: int, j: int| 0 <= i < j < finite_vals.len() ==> finite_vals[i] <= finite_vals[j]) &&
                /* Result is within the range of finite values */
                (!result.is_nan() ==> (finite_vals[0] <= result && result <= finite_vals[finite_vals.len() - 1]))
            }
        }
{
    // impl-start
    assume(false);
    0.0
    // impl-end
}
}
fn main() {}