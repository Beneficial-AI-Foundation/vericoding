/* Compute the absolute values element-wise for floating-point numbers. This function returns the absolute values (positive magnitude) of the data in x. Complex values are not handled, use absolute to find the absolute values of complex data. */

use vstd::prelude::*;

verus! {
fn fabs(x: Vec<f32>) -> (result: Vec<f32>)
    requires x.len() > 0,
    ensures 
        result.len() == x.len(),
        forall|i: int| 0 <= i < result.len() ==> {
            result[i] >= 0.0 &&
            result[i] == x[i].abs() &&
            result[i] == (-x[i]).abs()
        }
{
    // impl-start
    assume(false);
    Vec::new()
    // impl-end
}
}
fn main() {}