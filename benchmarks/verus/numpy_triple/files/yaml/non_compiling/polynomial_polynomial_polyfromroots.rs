/* Generate a monic polynomial with given roots.

Specification: polyfromroots generates a monic polynomial with given roots.
The resulting polynomial has the form p(x) = (x - r_0)(x - r_1)...(x - r_n),
where the coefficients are returned in ascending order of powers. */

use vstd::prelude::*;

verus! {
fn polyfromroots(roots: Vec<f32>) -> (coeffs: Vec<f32>)
    ensures 
        coeffs.len() == roots.len() + 1,
        coeffs[coeffs.len() - 1] == 1.0,
        forall|i: int| 0 <= i < roots.len() ==> 
            exists|eval_poly: spec_fn(f32) -> f32| 
                forall|x: f32| (eval_poly(x) == 0.0) == (x == roots[i])
{
    // impl-start
    assume(false);
    Vec::new()
    // impl-end
}
}
fn main() {}