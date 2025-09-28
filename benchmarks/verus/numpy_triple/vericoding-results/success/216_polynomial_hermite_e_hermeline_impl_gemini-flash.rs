// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn hermeline(off: f64, scl: f64) -> (coeffs: Vec<f64>)
    ensures
        coeffs@.len() == 2,
        coeffs@[0] == off,
        (scl == 0.0 ==> coeffs@[1] == 0.0),
        (scl != 0.0 ==> coeffs@[1] == scl)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 2): fixed postcondition related to `coeffs` length not being exactly 2 and corrected logic to push `scl` regardless of its value */
{
    let mut coeffs: Vec<f64> = Vec::new();
    coeffs.push(off);
    coeffs.push(scl);
    coeffs
}
// </vc-code>

}
fn main() {}