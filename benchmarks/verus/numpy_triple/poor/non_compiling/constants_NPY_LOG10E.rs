/* Base 10 logarithm of Euler's number e

NPY_LOG10E returns the base 10 logarithm of e with correct mathematical properties
log10(e) = 0.434294481903251827651128918916605082 */

use vstd::prelude::*;

verus! {
fn npy_log10e() -> (result: f64)
    ensures
        result == 0.434294481903251827651128918916605082,
        (10.0f64.powf(result) - 2.718281828459045).abs() < 1e-15,
        (result * 10.0f64.ln() - 1.0).abs() < 1e-15,
        result > 0.0,
        result < 1.0
{
    // impl-start
    assume(false);
    0.0
    // impl-end
}
}
fn main() {}