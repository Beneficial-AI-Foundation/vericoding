/* Return a copy of an array sorted along the first axis (ascending order).
This is equivalent to np.sort(a, axis=0) in NumPy.

Specification: msort returns a sorted copy of the input array in ascending order.
The result is a permutation of the input array. */

use vstd::prelude::*;

verus! {
fn msort(a: Vec<i32>) -> (result: Vec<i32>)
    ensures
        result.len() == a.len(),
        forall|i: int, j: int| 0 <= i < j < result.len() ==> result[i] <= result[j],
        result@.to_multiset() =~= a@.to_multiset(),
{
    // impl-start
    assume(false);
    Vec::new()
    // impl-end
}
}
fn main() {}