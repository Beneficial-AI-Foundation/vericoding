// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): kept existing helper function */
fn abs_f32(x: f32) -> (r: f32) {
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
    /* code modified by LLM (iteration 3): replaced Rust slice syntax with Verus' subrange method */
    let mut i: usize = c.len();
    while i > 0
        invariant
            0 <= i <= c.len(),
        decreases i
    {
        if abs_f32(c[i - 1]) < tol {
            i = i - 1;
        } else {
            break;
        }
    }

    if i == 0 {
        let mut result = Vec::new();
        result.push(0.0);
        result
    } else {
        let result = c.subrange(0, i);
        result
    }
}
// </vc-code>

}
fn main() {}