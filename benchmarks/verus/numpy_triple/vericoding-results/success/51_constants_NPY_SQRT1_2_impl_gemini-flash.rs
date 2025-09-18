// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn NPY_SQRT1_2() -> (result: f64)
// </vc-spec>
// <vc-code>
{
    // Derived from numpy/numpy/core/include/numpy/npy_math.h
    // #define NPY_SQRT1_2       0.707106781186547524401
    // Using `core::f64::consts::FRAC_1_SQRT_2` to ensure consistent value definition.
    // Note that `core::f64::consts::FRAC_1_SQRT_2` is not directly verifiable in Verus
    // so the value must be manually specified and verified against known constants from other sources.

    let val: f64 = 0.707106781186547524401f64;
    val
}
// </vc-code>

}
fn main() {}