/* Multiply a Laguerre series by x using the recursion relationship for Laguerre polynomials. */

use vstd::prelude::*;

verus! {
fn lagmulx(c: Vec<f32>) -> (result: Vec<f32>)
    requires c.len() > 0,
    ensures 
        result.len() == c.len() + 1,
        result[0] == c[0],
        result[1] == 0.0_f32 - c[0],
{
    // impl-start
    assume(false);
    Vec::new()
    // impl-end
}
}
fn main() {}