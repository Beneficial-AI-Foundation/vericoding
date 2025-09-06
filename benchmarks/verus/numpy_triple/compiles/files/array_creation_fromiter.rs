/* Create a new 1-dimensional array from an iterable object.
Takes the first n elements from the iterable sequence and creates a Vector.
This models numpy.fromiter with explicit count parameter.

Specification: fromiter creates a Vector containing the first n elements 
from the iterable in order. The resulting Vector has exactly n elements,
and each element at index i equals the i-th element from the iterable. */

use vstd::prelude::*;

verus! {
fn fromiter<A>(n: usize, iter: spec_fn(usize) -> A) -> (result: Vec<A>)
    requires n < usize::MAX,
    ensures
        result.len() == n,
        forall|i: int| 0 <= i < n ==> result[i as int] == iter(i as usize),
{
    // impl-start
    assume(false);
    Vec::new()
    // impl-end
}
}
fn main() {}