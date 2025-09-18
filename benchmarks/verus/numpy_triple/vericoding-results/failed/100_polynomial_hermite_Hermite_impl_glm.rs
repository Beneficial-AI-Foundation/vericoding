// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): changed current_degree parameter from int to usize */
fn next_hermite(h_prev: f32, h_prev_prev: f32, x: f32, current_degree: usize) -> (res: f32)
    requires current_degree >= 2,
{
    let deg_float = current_degree as f32;
    2.0 * x * h_prev - 2.0 * (deg_float - 1.0) * h_prev_prev
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
/* code modified by LLM (iteration 5): changed loop variable to usize and removed int casts */
{
    let n = coef.len();
    if n == 1 {
        coef[0]
    } else {
        let mut res = 0.0;
        let mut h0 = 1.0;   // H_0
        let mut h1 = 2.0 * x; // H_1

        // Add term for degree 0
        res += coef[0] * h0;

        // Add term for degree 1
        res += coef[1] * h1;

        // For degrees from 2 to n-1
        let mut i: usize = 2;
        while i < n
            invariant 2 <= i <= n,
            decreases n - i,
        {
            let h_next = next_hermite(h1, h0, x, i);
            res += coef[i] * h_next;

            // update for next iteration
            h0 = h1;
            h1 = h_next;

            i += 1;
        }

        res
    }
}
// </vc-code>

}
fn main() {}