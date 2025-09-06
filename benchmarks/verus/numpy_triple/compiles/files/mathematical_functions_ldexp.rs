/* Returns x1 * 2**x2, element-wise
The mantissas x1 and twos exponents x2 are used to construct floating point numbers x1 * 2**x2.

Returns x1 * 2**x2, element-wise.
The mantissas x1 and twos exponents x2 are used to construct floating point numbers x1 * 2**x2.

Specification: ldexp returns x1 * 2**x2 element-wise */

use vstd::prelude::*;

verus! {
fn ldexp(x1: Vec<f64>, x2: Vec<i32>) -> (result: Vec<f64>)
    requires x1.len() == x2.len(),
    ensures
        result.len() == x1.len(),
{
    // impl-start
    assume(false);
    Vec::new()
    // impl-end
}
}
fn main() {}