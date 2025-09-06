/* numpy.argwhere: Find the indices of array elements that are non-zero, grouped by element.

For a 1D vector, returns a list of indices where elements are non-zero.
Each index corresponds to a position in the original vector where the element is non-zero.
The returned indices are in the same order as they appear in the original vector.

Specification: numpy.argwhere returns all indices of non-zero elements.

Precondition: True (no special requirements)
Postcondition: 
1. All returned indices correspond to non-zero elements in the input vector
2. All non-zero elements in the input vector have their indices in the result
3. The result contains no duplicate indices
4. The indices are ordered according to their position in the original vector */

use vstd::prelude::*;

verus! {
fn numpy_argwhere(a: &Vec<f32>) -> (result: Vec<usize>)
    ensures
        forall|i: int| 0 <= i < result.len() ==> #[trigger] result[i] < a.len(),
        forall|i: int| 0 <= i < result.len() ==> a[#[trigger] result[i] as int] != 0.0f32,
        forall|i: int| 0 <= i < a.len() && a[i] != 0.0f32 ==> exists|j: int| 0 <= j < result.len() && #[trigger] result[j] == i,
        forall|i: int, j: int| 0 <= i < j < result.len() ==> #[trigger] result[i] < #[trigger] result[j],
{
    // impl-start
    assume(false);
    Vec::new()
    // impl-end
}
}
fn main() {}