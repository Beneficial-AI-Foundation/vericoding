/* Multiply one Laguerre series by another.

This function multiplies two Laguerre series represented as coefficient vectors.
The arguments are sequences of coefficients, from lowest order term to highest.
Returns the product of the two series as a new coefficient vector.

The multiplication of Laguerre polynomials results in terms that may not be
in the original Laguerre basis set, so the result represents the product
reprojected onto the Laguerre basis. */

use vstd::prelude::*;

verus! {
fn lagmul(c1: &Vec<f64>, c2: &Vec<f64>) -> (result: Vec<f64>)
    requires 
        c1.len() > 0,
        c2.len() > 0,
    ensures 
        result.len() == c1.len() + c2.len() - 1,
        forall|i: int| 0 <= i < result.len() && result[i] != 0.0 ==> 
            exists|j: int, k: int| 
                0 <= j < c1.len() && 
                0 <= k < c2.len() && 
                j + k == i && 
                c1[j] != 0.0 && 
                c2[k] != 0.0,
{
    // impl-start
    assume(false);
    Vec::new()
    // impl-end
}
}
fn main() {}