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
    /* code modified by LLM (iteration 4): directly push scl without conditional */
    let mut coeffs = Vec::new();
    coeffs.push(off);
    coeffs.push(scl);
    assert(coeffs@.len() == 2);
    assert(coeffs@[0] == off);
    assert(coeffs@[1] == scl);
    assert(scl == 0.0 ==> coeffs@[1] == 0.0);
    assert(scl != 0.0 ==> coeffs@[1] == scl);
    coeffs
}
// </vc-code>

}
fn main() {}