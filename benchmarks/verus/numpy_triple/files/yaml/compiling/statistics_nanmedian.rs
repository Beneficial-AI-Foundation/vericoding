/* Compute the median along the specified axis, ignoring NaNs.
Returns the median of the array elements.
For a vector V of length N, the median is the middle value of a sorted copy of V
(ignoring NaN values), when N is odd, and the average of the two middle values when N is even.
If all values are NaN, returns NaN. */

use vstd::prelude::*;

verus! {
spec fn all_nan(a: Seq<f32>) -> bool {
    forall|i: int| #![auto] 0 <= i < a.len() ==> (a[i] != a[i])
}

spec fn has_finite_value(a: Seq<f32>) -> bool {
    exists|i: int| #![auto] 0 <= i < a.len() && (a[i] == a[i])
}

fn nanmedian(a: Vec<f32>) -> (result: f32)
    ensures
        (all_nan(a@) ==> (result != result)) &&
        (has_finite_value(a@) ==> (result == result))
{
    // impl-start
    assume(false);
    0.0
    // impl-end
}
}
fn main() {}