/* Creates a Legendre series representation of a straight line `off + scl*x`.

This function generates the correct Legendre series coefficients for a linear function.
The Legendre series whose graph is a straight line is represented as a vector
where the coefficients correspond to the linear polynomial off + scl*x.

Parameters:
- off, scl: scalars representing the line off + scl*x

Returns:
- A vector of Float values representing the Legendre series coefficients

The specification ensures that the resulting coefficients correctly represent
the linear function. */

use vstd::prelude::*;

verus! {
fn legline(off: f64, scl: f64) -> (result: Vec<f64>)
    ensures
        result.len() == 2,
        result[0] == off,
        result[1] == scl,
{
    // impl-start
    assume(false);
    Vec::new()
    // impl-end
}
}
fn main() {}