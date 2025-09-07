/* IEEE 754 floating point representation of positive zero.

DEPRECATED: Removed from main namespace in NumPy 2.0. Use 0.0 instead.

IEEE 754 floating point representation of positive zero

Specification: PZERO represents IEEE 754 positive zero with the following properties:
1. It equals the standard zero value
2. It behaves as the additive identity
3. It behaves as expected in multiplication and division
4. It has special IEEE 754 properties (e.g., 1.0 / PZERO = +∞) */

use vstd::prelude::*;

verus! {
fn pzero() -> (result: f64)
    ensures result == 0.0
{
    // impl-start
    assume(false);
    0.0
    // impl-end
}
}
fn main() {}