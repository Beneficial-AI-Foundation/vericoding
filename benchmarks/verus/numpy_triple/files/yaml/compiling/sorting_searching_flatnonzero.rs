/* numpy.flatnonzero: Return indices that are non-zero in the flattened version of a.

This function returns the indices of all non-zero elements in the array.
The returned indices correspond to positions in the flattened array where
the elements are non-zero.

For example, if array is [1, 0, 3, 0, 5], the function returns [0, 2, 4]
indicating that elements at positions 0, 2, and 4 are non-zero.

Specification: flatnonzero returns indices of all non-zero elements.

Precondition: True (no restrictions on input array)
Postcondition: 
1. All returned indices correspond to non-zero elements in the original array
2. All non-zero elements in the original array have their indices in the result
3. The result contains no duplicate indices
4. The result indices are sorted in ascending order */

use vstd::prelude::*;

verus! {
fn flatnonzero(a: Vec<f64>) -> (result: Vec<usize>)
    ensures
        /* All indices in result point to non-zero elements */
        forall|i: int| 0 <= i < result.len() ==> a[result[i] as int] != 0.0,
        /* All non-zero elements have their indices in result */
        forall|j: int| 0 <= j < a.len() && a[j] != 0.0 ==> exists|k: int| 0 <= k < result.len() && result[k] == j,
        /* Result contains no duplicate indices */
        forall|i: int, j: int| 0 <= i < result.len() && 0 <= j < result.len() && i != j ==> result[i] != result[j],
        /* Result indices are sorted in ascending order */
        forall|i: int, j: int| 0 <= i < j < result.len() ==> result[i] < result[j],
{
    // impl-start
    assume(false);
    Vec::new()
    // impl-end
}
}
fn main() {}