// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): fixed syntax error by adding curly braces to function signature */
spec fn hermite_polynomial(coef: Vec<f32>, x: f32, n: nat) -> f32
    decreases n
{
    if n == 0 {
        if coef.len() > 0 { coef[0] } else { 0.0 }
    } else if n >= coef.len() {
        0.0
    } else {
        coef[n] + x * hermite_polynomial(coef, x, n - 1)
    }
}

fn hermite_eval_recursive(coef: Vec<f32>, x: f32, index: usize) -> (result: f32)
    requires index < coef.len(),
    requires coef.len() > 0,
    decreases coef.len() - index
{
    if index == coef.len() - 1 {
        coef[index]
    } else {
        coef[index] + x * hermite_eval_recursive(coef, x, index + 1)
    }
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
    /* code modified by LLM (iteration 5): kept simple implementation */
    if coef.len() == 1 {
        coef[0]
    } else {
        hermite_eval_recursive(coef, x, 0)
    }
}
// </vc-code>

}
fn main() {}