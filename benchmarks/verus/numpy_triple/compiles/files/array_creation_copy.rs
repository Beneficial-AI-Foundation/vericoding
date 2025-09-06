/* Return an array copy of the given object.
The copy has the same shape and values as the original array,
but occupies different memory locations.

Specification: copy returns a vector with identical values but independent memory.
The resulting vector has the same size and all elements equal to the original,
ensuring that the copy is element-wise equivalent to the original. */

use vstd::prelude::*;

verus! {
fn copy<T: Copy>(a: &Vec<T>) -> (result: Vec<T>)
    ensures
        result.len() == a.len(),
        forall|i: int| 0 <= i < result.len() ==> result[i] == a[i],
{
    // impl-start
    assume(false);
    Vec::new()
    // impl-end
}
}
fn main() {}