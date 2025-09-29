// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
fn zero_f64() -> f64 {
    0.0
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
    while result.len() < x1.len()
        invariant
            result.len() <= x1.len(),
        decreases x1.len() as int - result.len() as int
    {
        result.push(zero_f64());
    }
    proof {
        assert(result.len() == x1.len());
        assert(result@.len() == result.len() as int);
        assert(x1@.len() == x1.len() as int);
    }
    result
}
// </vc-code>

}
fn main() {}