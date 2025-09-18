// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

proof fn helper_lemma_scl_zero(scl: f64)
    ensures scl == 0.0 ==> scl == 0.0
{
}

proof fn helper_lemma_scl_nonzero(scl: f64)
    ensures scl != 0.0 ==> scl != 0.0
{
}

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
    let mut coeffs = Vec::new();
    coeffs.push(off);
    coeffs.push(scl);
    proof {
        helper_lemma_scl_zero(scl);
        helper_lemma_scl_nonzero(scl);
    }
    coeffs
}
// </vc-code>

}
fn main() {}