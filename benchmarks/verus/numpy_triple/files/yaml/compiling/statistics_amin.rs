/* Return the minimum of an array or minimum along an axis.

This is an alias for numpy.min that returns the minimum value among all elements in the array.
Requires a non-empty array since there is no minimum of an empty set.

This is a reduction operation that finds the smallest value in the array.
NaN values are propagated - if any element is NaN, the result will be NaN.

Specification: amin returns the minimum element in the vector.

Precondition: True (non-empty constraint is enforced by type Vector Float (n + 1))
Postcondition: result is the minimum value and is an element of the vector

Properties:
1. The result is actually an element of the input vector
2. The result is less than or equal to all elements in the vector
3. This captures the mathematical definition of minimum */

use vstd::prelude::*;

verus! {
spec fn in_array(result: f32, a: Seq<f32>) -> bool {
    exists|i: int| 0 <= i < a.len() && result == a[i]
}

fn amin(a: Vec<f32>) -> (result: f32)
    requires a.len() > 0,
    ensures in_array(result, a@),
{
    // impl-start
    assume(false);
    0.0
    // impl-end
}
}

fn main() {}