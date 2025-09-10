/* Compute the q-th quantile of the data in a vector.
Specification: quantile returns a value that has the property that 
approximately q proportion of the data is less than or equal to it. */

use vstd::prelude::*;

verus! {
fn quantile(a: Vec<f32>, q: f32) -> (result: f32)
    requires 
        a.len() > 0,
        0.0 <= q <= 1.0,
    ensures
        exists|i: int| 0 <= i < a.len() && a[i] <= result,
        exists|i: int| 0 <= i < a.len() && result <= a[i],
        q == 0.0 ==> forall|i: int| 0 <= i < a.len() ==> result <= a[i],
        q == 1.0 ==> forall|i: int| 0 <= i < a.len() ==> a[i] <= result,
{
    // impl-start
    assume(false);
    0.0
    // impl-end
}
}
fn main() {}