// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): absolute value for f32 */
fn abs_f32(x: f32) -> f32 {
    if x < 0.0 { -x } else { x }
}

// </vc-helpers>

// <vc-spec>
fn trimcoef(c: Vec<f32>, tol: f32) -> (result: Vec<f32>)
    ensures
        result.len() >= 1,
        result.len() <= c.len(),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): trim trailing coefficients but ensure non-empty result */
    let mut cc = c;
    if cc.len() == 0 {
        let mut res: Vec<f32> = Vec::new();
        res.push(0.0);
        res
    } else {
        while cc.len() > 1 && abs_f32(cc[cc.len()-1]) <= tol
            invariant
                cc.len() <= c.len(),
            decreases cc.len()
        {
            cc.pop();
        }
        cc
    }
}
// </vc-code>

}
fn main() {}