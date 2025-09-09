/* Find the indices of array elements that are non-zero, grouped by element.

For a 1D vector, returns a list of indices where elements are non-zero.
Each index corresponds to a position in the original vector where the element is non-zero.
The returned indices are in the same order as they appear in the original vector.

This function is equivalent to finding all positions i such that a[i] ≠ 0.
The result is a list of indices, not suitable for direct array indexing but useful
for analysis and conditional processing. */

use vstd::prelude::*;

verus! {
fn argwhere(a: &Vec<f64>) -> (indices: Vec<usize>)
    ensures
        forall|i: int| 0 <= i < indices.len() ==> (#[trigger] indices[i]) < a.len(),
        forall|i: int| 0 <= i < indices.len() ==> a[indices[i] as int] != 0.0,
        forall|i: int| 0 <= i < a.len() && a[i] != 0.0 ==> exists|j: int| 0 <= j < indices.len() && indices[j] == i,
        forall|i: int, j: int| 0 <= i < indices.len() && 0 <= j < indices.len() && i != j ==> indices[i] != indices[j],
        forall|i: int, j: int| 0 <= i < indices.len() && 0 <= j < indices.len() && (indices[i] as int) < (indices[j] as int) ==> i < j,
        (indices.len() == 0) == (forall|i: int| 0 <= i < a.len() ==> a[i] == 0.0),
{
    // impl-start
    assume(false);
    Vec::new()
    // impl-end
}
}
fn main() {}