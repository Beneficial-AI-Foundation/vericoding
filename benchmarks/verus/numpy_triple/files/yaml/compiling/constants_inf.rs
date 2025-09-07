/* IEEE 754 floating point representation of (positive) infinity

Specification: inf represents positive infinity with the following properties:
1. inf is greater than any finite float value
2. inf + any finite value = inf
3. inf * positive finite value = inf
4. inf * negative finite value = -inf
5. inf / any finite non-zero value = inf (with appropriate sign) */

use vstd::prelude::*;

verus! {
/* IEEE 754 floating point representation of (positive) infinity */
fn inf() -> (result: f32)
{
    // impl-start
    assume(false);
    0.0
    // impl-end
}
}

fn main() {}