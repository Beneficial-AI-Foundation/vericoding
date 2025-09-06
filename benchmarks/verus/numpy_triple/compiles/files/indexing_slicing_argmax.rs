/* Returns the indices of the maximum values along an axis.

Returns the index of the maximum value in a non-empty vector (first occurrence).

Specification: argmax returns the index of the first maximum element
This comprehensive specification captures:
1. The returned index points to a maximum element
2. All elements to the left of the returned index are strictly less than the maximum
3. All elements to the right of the returned index are less than or equal to the maximum
4. The function returns the first occurrence of the maximum value
5. The returned index is valid (type-safe with Fin)
6. The result is deterministic for the same input */

use vstd::prelude::*;

verus! {
fn argmax(arr: &Vec<i32>) -> (result: usize)
    requires arr.len() > 0,
    ensures
        result < arr.len(),
        forall|i: int| 0 <= i < arr.len() ==> arr[i] <= arr[result as int],
        forall|i: int| 0 <= i < result ==> arr[i] < arr[result as int],
        forall|i: int| result < i < arr.len() ==> arr[i] <= arr[result as int],
        forall|j: int| 0 <= j < arr.len() && arr[j] == arr[result as int] ==> result <= j,
{
    // impl-start
    assume(false);
    0
    // impl-end
}
}
fn main() {}