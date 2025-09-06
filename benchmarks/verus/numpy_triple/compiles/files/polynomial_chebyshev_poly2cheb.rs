/* Convert a polynomial to a Chebyshev series.
    
This function converts coefficients of a polynomial in the standard monomial basis
(1, x, x², x³, ...) to coefficients in the Chebyshev polynomial basis
(T₀(x), T₁(x), T₂(x), T₃(x), ...).

The input polynomial coefficients are ordered from lowest degree to highest:
pol = [a₀, a₁, a₂, ..., aₙ] represents the polynomial a₀ + a₁x + a₂x² + ... + aₙxⁿ

The output Chebyshev coefficients are also ordered from lowest to highest degree:
result = [c₀, c₁, c₂, ..., cₙ] represents c₀T₀(x) + c₁T₁(x) + c₂T₂(x) + ... + cₙTₙ(x) */

use vstd::prelude::*;

verus! {
fn poly2cheb(pol: Vec<f64>) -> (result: Vec<f64>)
    ensures
        result.len() == pol.len(),
        pol.len() == 4 && pol[0] == 0.0 && pol[1] == 1.0 && pol[2] == 2.0 && pol[3] == 3.0 ==>
            result[0] == 1.0 && result[1] == 3.25 && result[2] == 1.0 && result[3] == 0.75,
        pol.len() > 1 && (forall|i: int| 2 <= i < pol.len() ==> pol[i] == 0.0) ==>
            result[0] == pol[0] && result[1] == pol[1],
        pol.len() == 3 && pol[0] == 0.0 && pol[1] == 0.0 && pol[2] == 1.0 ==>
            result[0] == 0.5 && result[1] == 0.0 && result[2] == 0.5,
        pol.len() == 4 && pol[0] == 0.0 && pol[1] == 0.0 && pol[2] == 0.0 && pol[3] == 1.0 ==>
            result[0] == 0.0 && result[1] == 0.75 && result[2] == 0.0 && result[3] == 0.25,
{
    // impl-start
    assume(false);
    Vec::new()
    // impl-end
}
}
fn main() {}