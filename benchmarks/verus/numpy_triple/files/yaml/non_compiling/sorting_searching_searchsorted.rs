/* numpy.searchsorted: Find indices where elements should be inserted to maintain order.

Given a sorted array `a` and values `v`, returns indices such that inserting 
each element of `v` at the corresponding index would preserve the sorted order of `a`.

This implementation focuses on the 'left' side behavior where for each value v[i],
it returns the leftmost suitable insertion position. The returned indices are
in the range [0, n] where n is the length of the sorted array.

Specification: numpy.searchsorted returns indices for sorted insertion.

Precondition: The input array `a` must be sorted in ascending order
Postcondition: For each element v[i], the returned index idx satisfies:
- All elements before idx are strictly less than v[i] (left insertion property)
- All elements at or after idx are greater than or equal to v[i] (sorted property)
- The index is valid for insertion (between 0 and n inclusive)
- Inserting v[i] at idx preserves the sorted order of the array */

use vstd::prelude::*;

verus! {
fn numpy_searchsorted(a: Vec<f32>, v: Vec<f32>) -> (result: Vec<usize>)
    requires 
        forall|i: int, j: int| 0 <= i < j < a.len() ==> a[i] <= a[j],
    ensures
        result.len() == v.len(),
        forall|k: int| 0 <= k < v.len() ==> {
            let idx = result[k] as int;
            &&& (0 <= idx <= a.len())
            &&& (forall|i: int| 0 <= i < a.len() && i < idx ==> a[i] < v[k])
            &&& (forall|j: int| 0 <= j < a.len() && idx <= j ==> v[k] <= a[j])
            &&& (forall|pos: int| 0 <= pos < idx ==> 
                    exists|i: int| 0 <= i < a.len() && i < pos && a[i] >= v[k])
        }
{
    // impl-start
    assume(false);
    Vec::new()
    // impl-end
}
}
fn main() {}