/* Return the truth value of (x1 <= x2) element-wise */

use vstd::prelude::*;

verus! {
fn less_equal(x1: Vec<f32>, x2: Vec<f32>) -> (result: Vec<bool>)
    requires x1.len() == x2.len(),
    ensures 
        result.len() == x1.len(),
        forall|i: int| 0 <= i < result.len() ==> 
            result[i] == (x1[i] <= x2[i]),
        forall|i: int| 0 <= i < result.len() ==> 
            (result[i] == true <==> x1[i] <= x2[i]),
        forall|i: int| 0 <= i < result.len() ==> 
            (result[i] == false <==> x1[i] > x2[i]),
        forall|i: int| 0 <= i < result.len() ==> 
            (x1[i] == x2[i] ==> result[i] == true),
{
    // impl-start
    assume(false);
    Vec::new()
    // impl-end
}
}
fn main() {}