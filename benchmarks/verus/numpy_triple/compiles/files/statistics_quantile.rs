/* Compute the q-th quantile of the data in a vector.

Specification: quantile returns a value that has the property that 
approximately q proportion of the data is less than or equal to it.

This is based on numpy.quantile which computes the q-th quantile of data along a specified axis.
The quantile must be between 0 and 1 inclusive, where 0 gives the minimum and 1 gives the maximum. */

use vstd::prelude::*;

verus! {
fn quantile(a: &Vec<i32>, q_num: i32, q_den: i32) -> (result: i32)
    requires 
        a.len() > 0,
        q_den > 0,
        0 <= q_num <= q_den,
    ensures
        (exists|i: int| 0 <= i < a.len() && a[i] <= result),
        (exists|i: int| 0 <= i < a.len() && result <= a[i]),
        (q_num == 0) ==> (forall|i: int| 0 <= i < a.len() ==> result <= a[i]),
        (q_num == q_den) ==> (forall|i: int| 0 <= i < a.len() ==> a[i] <= result),
{
    // impl-start
    assume(false);
    0
    // impl-end
}
}

fn main() {}