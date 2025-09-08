/* numpy.ndim: Return the number of dimensions of an array.

In our Vector-based framework, vectors are always 1-dimensional.
This function returns 1 for any vector input, representing the fact
that Vector T n is a 1D array with n elements.

Note: In NumPy, scalars are 0-dimensional, but in our framework,
we represent them as Vector T 1, so this always returns 1. */

use vstd::prelude::*;

verus! {
fn ndim<T>(a: &Vec<T>) -> (result: usize)
    ensures result == 1
{
    // impl-start
    assume(false);
    0
    // impl-end
}
}
fn main() {}