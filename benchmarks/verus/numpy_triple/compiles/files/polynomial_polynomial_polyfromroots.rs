/* Generate a monic polynomial with given roots.

The resulting polynomial has the form p(x) = (x - r_0)(x - r_1)...(x - r_n),
where the coefficients are returned in ascending order of powers.

This corresponds to the numpy.polynomial.polynomial.polyfromroots function
which generates a monic polynomial with given roots. The coefficient of the
highest degree term is always 1 for monic polynomials. */

use vstd::prelude::*;

verus! {
fn polyfromroots(roots: &Vec<f64>) -> (result: Vec<f64>)
    ensures
        result.len() == roots.len() + 1,
        result[result.len() - 1] == 1.0,
{
    // impl-start
    assume(false);
    Vec::new()
    // impl-end
}
}
fn main() {}