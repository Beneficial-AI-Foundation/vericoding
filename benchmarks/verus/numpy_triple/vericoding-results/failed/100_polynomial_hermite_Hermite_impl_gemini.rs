// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): removed unsupported is_finite and corrected requires */
fn horner_tailrec(coef: &Vec<f32>, x: f32, i: usize, acc: f32) -> (result: f32)
    requires
        i <= coef.len(),
    ensures true,
    decreases i
{
    if i == 0 {
        acc
    } else {
        let new_acc = acc * x + coef[i-1];
        horner_tailrec(coef, x, i - 1, new_acc)
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
    /* code modified by LLM (iteration 5): removed unsupported is_finite calls */
    let n = coef.len();

    if n == 1 {
        return coef[0];
    }

    let mut acc = coef[n-1];
    let mut i: usize = n - 1;
    while i > 0
        invariant
            0 < i < n,
        decreases i
    {
        i = i - 1;
        acc = acc * x + coef[i];
    }
    acc
}
// </vc-code>

}
fn main() {}