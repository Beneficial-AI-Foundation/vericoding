/* numpy.nanargmax: Returns the index of the maximum value in a vector, ignoring NaN values.

Returns the index of the maximum value among all non-NaN elements in the array.
Requires that at least one element is not NaN, otherwise it would raise an error.

In case of multiple occurrences of the maximum values, the indices
corresponding to the first occurrence are returned.

This function returns the position of the largest non-NaN element in the array.

Specification: numpy.nanargmax returns the index of the maximum non-NaN element.

Precondition: At least one element is not NaN
Postcondition: The element at the returned index is not NaN, is the maximum 
among all non-NaN values, and is the first occurrence of such maximum value. */

use vstd::prelude::*;

verus! {
fn nanargmax(a: Vec<f32>) -> (idx: usize)
    requires 
        a.len() > 0,
        exists|i: int| 0 <= i < a.len() && !a[i].is_nan(),
    ensures 
        idx < a.len(),
        !a[idx as int].is_nan(),
        forall|j: int| 0 <= j < a.len() && !a[j].is_nan() ==> a[j] <= a[idx as int],
        forall|j: int| 0 <= j < a.len() && !a[j].is_nan() && a[j] == a[idx as int] ==> idx <= j,
{
    // impl-start
    assume(false);
    0
    // impl-end
}
}
fn main() {}