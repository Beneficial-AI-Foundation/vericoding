/* Returns element-wise True where signbit is set (less than zero). Returns element-wise True where signbit is set (less than zero). Specification: signbit returns True for negative numbers and False for non-negative numbers */

use vstd::prelude::*;

verus! {
fn signbit(x: Vec<f32>) -> (result: Vec<bool>)
    requires x.len() > 0,
    ensures 
        result.len() == x.len(),
        forall|i: int| 0 <= i < x.len() ==> result[i] == (x[i] < 0.0)
{
    // impl-start
    assume(false);
    Vec::new()
    // impl-end
}
}
fn main() {}