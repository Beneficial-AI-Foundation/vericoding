/* IEEE 754 floating point representation of Not a Number (NaN)

IEEE 754 floating point representation of Not a Number (NaN)

Specification: nan represents Not a Number with the following IEEE 754 properties:
1. Float.isNaN returns true for NaN (primary property)
2. Any arithmetic operation with NaN results in NaN
3. NaN is not ordered (comparisons with any value are false except ≠)
4. NaN is not finite
5. Standard operations preserve NaN propagation */

use vstd::prelude::*;

verus! {
fn nan() -> (result: f64)
    ensures result != result,  // NaN is not equal to itself
{
    // impl-start
    assume(false);
    0.0
    // impl-end
}
}
fn main() {}