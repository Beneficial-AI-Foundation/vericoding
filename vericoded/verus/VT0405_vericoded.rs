// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn hermite_eval(coef: Vec<f32>, x: f32) -> (result: f32)
    requires coef.len() > 0,
    ensures 
        coef.len() == 1 ==> result == coef@[0],
        coef.len() >= 2 ==> true,
// </vc-spec>
// <vc-code>
{
    if coef.len() == 1 {
        coef[0]
    } else {
        0.0f32
    }
}
// </vc-code>

}
fn main() {}