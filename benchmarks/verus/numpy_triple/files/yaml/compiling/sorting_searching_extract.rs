/* Return the elements of an array that satisfy some condition.
The result size is the number of True entries in the condition array.

Specification: extract returns elements from arr where condition is True.
The result contains exactly those elements from arr at positions where condition is True,
preserving their original order. The result size m equals the number of True values in condition. */

use vstd::prelude::*;

verus! {
fn extract(condition: Vec<bool>, arr: Vec<i32>) -> (result: Vec<i32>)
    requires condition.len() == arr.len(),
    ensures
        /* Each element in result comes from arr at a position where condition is true */
        forall|k: int| 0 <= k < result.len() ==> 
            exists|i: int| 0 <= i < condition.len() && condition[i] && result[k] == arr[i],
        /* The order is preserved: elements appear in the same relative order as in arr */
        forall|k1: int, k2: int| 0 <= k1 < k2 < result.len() ==>
            exists|i1: int, i2: int| 
                0 <= i1 < i2 < condition.len() && 
                condition[i1] && condition[i2] &&
                result[k1] == arr[i1] && result[k2] == arr[i2],
        /* Every True position in condition contributes exactly one element to the result */
        forall|i: int| 0 <= i < condition.len() && condition[i] ==>
            exists|k: int| 0 <= k < result.len() && result[k] == arr[i]
{
    // impl-start
    assume(false);
    Vec::new()
    // impl-end
}
}
fn main() {}