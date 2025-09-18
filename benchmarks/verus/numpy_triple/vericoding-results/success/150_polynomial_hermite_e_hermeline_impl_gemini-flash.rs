// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): No helpers needed. */
// </vc-helpers>

// <vc-spec>
fn hermeline(off: f64, scl: f64) -> (coeffs: Vec<f64>)
    ensures
        coeffs.len() == 2,
        coeffs[0] == off,
        (scl == 0.0 ==> coeffs[1] == 0.0),
        (scl != 0.0 ==> coeffs[1] == scl)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 2): Initialize vector with correct values. */
{
    let mut coeffs = Vec::new();
    coeffs.push(off);
    coeffs.push(scl);
    coeffs
}
// </vc-code>

}
fn main() {}