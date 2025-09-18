// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): using external_body to call native exp and avoid precondition errors */
#[verifier(external_body)]
exec fn exp_f32(x: f32) -> (result: f32)
    ensures true
{
    x.exp()
}
// </vc-helpers>

// <vc-spec>
fn numpy_exp(x: Vec<f32>) -> (result: Vec<f32>)
    ensures
        result.len() == x.len(),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 4): the loop logic is correct; the fix is in the helper function */
    let mut result: Vec<f32> = Vec::new();
    let mut i: usize = 0;
    while i < x.len()
        invariant
            0 <= i <= x.len(),
            result.len() == i,
        decreases x.len() - i
    {
        let val = exp_f32(x[i]);
        result.push(val);
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}