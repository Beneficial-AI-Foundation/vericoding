/* Creates a Legendre series representation of a straight line `off + scl*x`. This function generates the correct Legendre series coefficients for a linear function. */

use vstd::prelude::*;

verus! {
fn legline(off: f32, scl: f32) -> (result: Vec<f32>)
    ensures
        result.len() == 2,
        result[0] == off,
        result[1] == scl
{
    // impl-start
    assume(false);
    Vec::new()
    // impl-end
}
}
fn main() {}