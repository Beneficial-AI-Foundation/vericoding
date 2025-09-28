// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): simple reciprocal computation without preconditions */
fn compute_recip(x: f32) -> f32 {
    1.0f32 / x
}
// </vc-helpers>

// <vc-spec>
fn numpy_reciprocal(x: Vec<f32>) -> (result: Vec<f32>)
    requires 
        x.len() > 0,
        forall|i: int| 0 <= i < x@.len() ==> x@[i] != 0.0f32,
    ensures
        result@.len() == x@.len(),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): implement loop to compute reciprocals; avoid spec-only assertions; maintain length invariants */
    let n: usize = x.len();
    let mut result: Vec<f32> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            i <= n,
            result@.len() == i as int,
            (x@).len() == n as int,
        decreases n as int - i as int
    {
        let xi = x[i];
        let yi = compute_recip(xi);
        result.push(yi);
        i += 1;
    }
    result
}
// </vc-code>

}
fn main() {}