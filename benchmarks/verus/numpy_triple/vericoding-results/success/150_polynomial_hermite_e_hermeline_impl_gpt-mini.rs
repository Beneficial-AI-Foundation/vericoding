// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): placeholder helper */
spec fn helper_placeholder() -> int { 0 }
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
{
    /* code modified by LLM (iteration 2): construct vector of two coefficients and prove postconditions */
    let mut coeffs: Vec<f64> = Vec::new();
    coeffs.push(off);
    coeffs.push(scl);
    proof {
        assert(coeffs.len() == 2);
        assert(coeffs[0] == off);
        if scl == 0.0 {
            assert(coeffs[1] == 0.0);
        } else {
            assert(coeffs[1] == scl);
        }
    }
    coeffs
}
// </vc-code>

}
fn main() {}