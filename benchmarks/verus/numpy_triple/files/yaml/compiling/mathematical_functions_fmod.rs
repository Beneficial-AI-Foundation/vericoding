/* Returns the element-wise remainder of division where the remainder has the same sign as the dividend */

use vstd::prelude::*;

verus! {
fn fmod(x1: &Vec<f32>, x2: &Vec<f32>) -> (result: Vec<f32>)
    requires x1.len() == x2.len(),
    ensures result.len() == x1.len()
{
    // impl-start
    assume(false);
    Vec::new()
    // impl-end
}
}
fn main() {}