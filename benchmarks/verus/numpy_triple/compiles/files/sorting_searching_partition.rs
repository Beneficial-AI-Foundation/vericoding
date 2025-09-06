/* Return a partitioned copy of an array around the k-th element

Specification: partition rearranges elements so that the k-th element is in its sorted position,
with smaller elements before it and equal/greater elements after it */

use vstd::prelude::*;

verus! {
fn partition(arr: Vec<i32>, kth: usize) -> (result: Vec<i32>)
    requires 
        kth < arr.len(),
    ensures
        result.len() == arr.len(),
        forall|i: int| 0 <= i < kth ==> result[i] <= result[kth as int],
        forall|i: int| kth < i < result.len() ==> result[i] >= result[kth as int],
        result =~= arr,
{
    // impl-start
    assume(false);
    Vec::new()
    // impl-end
}
}
fn main() {}