/* Return the number of elements along a given axis

Parameters
----------
a : array_like
    Input data.
axis : int, optional
    Axis along which the elements are counted. By default, give
    the total number of elements.

Returns
-------
element_count : int
    Number of elements along the specified axis.

Returns the number of elements in a vector

Specification: size returns the length of the vector, which is its type parameter n */

use vstd::prelude::*;

verus! {
fn size<const N: usize>(a: &[f64; N]) -> (result: usize)
    requires true,
    ensures result == N,
{
    // impl-start
    assume(false);
    0
    // impl-end
}
}
fn main() {}