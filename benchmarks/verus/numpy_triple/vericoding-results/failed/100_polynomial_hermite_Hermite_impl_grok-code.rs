// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Added decreases clause for the while loop to fix verification failure */
fn hermite_exec(n: usize, x: f32) -> f32 {
    if n == 0 {
        1.0
    } else if n == 1 {
        2.0 * x
    } else {
        let mut h0 = 1.0;
        let mut h1 = 2.0 * x;
        let mut coeff = 0.0;
        let mut current_n = 1;
        while current_n + 1 <= n
            decreases n - current_n
        {
            coeff = coeff + 2.0;
            let h_next = 2.0 * x * h1 - coeff * h0;
            h0 = h1;
            h1 = h_next;
            current_n = current_n + 1;
        }
        h1
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
    /* code modified by LLM (iteration 5): No changes needed as helpers fixed */
    let mut sum = 0.0;
    for i in 0..coef.len() {
        sum += coef[i] * hermite_exec(i, x);
    }
    sum
}
// </vc-code>

}
fn main() {}