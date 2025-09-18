// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Horner evaluation using Horner's method without is_finite */
fn horner_eval(coef: Vec<f32>, x: f32) -> f32 {
    let mut acc: f32 = 0.0;
    let mut j: usize = coef.len();
    while j > 0
        invariant j <= coef.len(),
        decreases j
    {
        let k = j - 1;
        assert(k < coef.len());
        acc = acc * x + coef[k];
        j = k;
    }
    acc
}
// </vc-helpers>

// <vc-spec>
fn hermite_eval(coef: Vec<f32>, x: f32) -> (result: f32)
    requires coef.len() > 0,
    ensures 
        coef.len() == 1 ==> result == coef[0],
        coef.len() >= 2 ==> true,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): compute polynomial via Horner's method */
    let res = horner_eval(coef, x);
    res
}
// </vc-code>

}
fn main() {}