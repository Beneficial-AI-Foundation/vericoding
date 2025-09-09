/* numpy.shape: Return the shape of an array.

For a one-dimensional vector, returns its length as a natural number.
This corresponds to the single element in the shape tuple for 1D arrays
in NumPy.

In the general NumPy implementation, shape returns a tuple of dimensions.
For our Vector type, which is inherently one-dimensional, the shape is
simply the length parameter n.

Specification: numpy.shape returns the length of the vector.

For a Vector of length n, the shape function returns n.
This captures the fundamental property that the shape of a 1D array
is its length.

Precondition: True (shape is defined for all vectors)
Postcondition: The result equals the length parameter n of the vector */

use vstd::prelude::*;

verus! {
fn shape<T>(a: &Vec<T>) -> (result: usize)
    ensures result == a.len()
{
    // impl-start
    assume(false);
    0
    // impl-end
}
}
fn main() {}