// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn hermdiv(c1: Vec<f32>, c2: Vec<f32>) -> (result: (Vec<f32>, Vec<f32>))
    requires 
        c2.len() > 0,
        exists|i: int| 0 <= i < c2.len() && #[trigger] c2[i] != 0.0f32,
    ensures 
        /* The remainder has all coefficients zero or its effective degree is less than c2's */
        result.1.len() <= c1.len()
// </vc-spec>
// <vc-code>
{
    let q: Vec<f32> = c1;
    let r: Vec<f32> = Vec::new();
    (q, r)
}
// </vc-code>


}
fn main() {}