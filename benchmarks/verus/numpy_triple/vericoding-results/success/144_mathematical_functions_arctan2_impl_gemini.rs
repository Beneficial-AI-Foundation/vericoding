// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
#[verifier(external_body)]
fn compute_arctan2(y: f64, x: f64) -> f64 {
    y.atan2(x)
}
// </vc-helpers>

// <vc-spec>
fn numpy_arctan2(x1: &Vec<f64>, x2: &Vec<f64>) -> (result: Vec<f64>)
    requires x1@.len() == x2@.len(),
    ensures result@.len() == x1@.len(),
// </vc-spec>
// <vc-code>
{
    let mut result: Vec<f64> = Vec::new();
    let mut i: usize = 0;
    while i < x1.len()
        invariant
            x1@.len() == x2@.len(),
            i <= x1@.len(),
            result@.len() == i
        decreases x1.len() - i
    {
        let r = compute_arctan2(x1[i], x2[i]);
        result.push(r);
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}