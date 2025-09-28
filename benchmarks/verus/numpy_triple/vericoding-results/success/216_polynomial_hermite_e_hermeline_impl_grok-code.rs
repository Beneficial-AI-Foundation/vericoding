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
{
    let mut coeffs: Vec<f64> = Vec::new();
    coeffs.push(off);
    coeffs.push(scl);
    proof {
        assert(coeffs@.len() == 2);
        assert(coeffs@[0] == off);
        if scl == 0.0 {
            assert(coeffs@[1] == 0.0);
        }
        else {
            assert(coeffs@[1] == scl);
        }
    }
    coeffs
}
// </vc-code>

}
fn main() {}