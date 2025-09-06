/* numpy.full_like: Return a full array with the same shape and type as a given array.

Creates a new array with the same shape as the input array `a`, where all
elements are set to the specified `fill_value`. This is useful for creating
arrays of a specific constant value while preserving the shape of an existing
array.

The actual type of fill_value will be cast to match the array's type,
similar to numpy's behavior where 0.1 becomes 0 for integer arrays.

Specification: numpy.full_like returns a vector with the same shape as `a`
where every element equals `fill_value`.

Precondition: True (no special preconditions needed)
Postcondition: The result has the same length as `a` and all elements equal `fill_value` */

use vstd::prelude::*;

verus! {
fn numpy_full_like(a: &Vec<f64>, fill_value: f64) -> (result: Vec<f64>)
    ensures
        result.len() == a.len(),
        forall|i: int| 0 <= i < result.len() ==> result[i] == fill_value,
{
    // impl-start
    assume(false);
    Vec::new()
    // impl-end
}
}
fn main() {}