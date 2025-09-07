/* Returns the number of elements in a vector

Specification: size returns the length of the vector, which is its type parameter n */

use vstd::prelude::*;

verus! {
fn size(a: &Vec<f64>) -> (result: usize)
    ensures result == a.len()
{
    // impl-start
    assume(false);
    0
    // impl-end
}
}
fn main() {}