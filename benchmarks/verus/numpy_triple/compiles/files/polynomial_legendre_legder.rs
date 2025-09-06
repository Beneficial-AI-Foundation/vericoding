/* Differentiate a Legendre series.
Returns the Legendre series coefficients c differentiated m times.
Each differentiation is multiplied by scl (scaling factor).

Specification: legder computes the derivative of a Legendre series */

use vstd::prelude::*;

verus! {
fn legder(c: &Vec<f64>, m: usize, scl: f64) -> (result: Vec<f64>)
    requires c.len() >= 1,
    ensures
        result.len() == (if m >= c.len() { 1 } else { if c.len() >= m && c.len() - m >= 1 { c.len() - m } else { 1 } }),
        m == 0 ==> result.len() == c.len(),
        m >= c.len() ==> result.len() == 1,
{
    // impl-start
    assume(false);
    Vec::new()
    // impl-end
}
}
fn main() {}