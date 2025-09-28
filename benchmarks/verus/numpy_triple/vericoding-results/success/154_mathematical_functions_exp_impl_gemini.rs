// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
#[verifier(external_body)]
fn exp_f32(x: f32) -> f32 {
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
    /* code modified by LLM (iteration 2): Changed loop counter from 'nat' to 'usize' to resolve compilation errors related to type casting for array indexing and arithmetic. */
    let mut result = Vec::new();
    let mut i: usize = 0;
    while i < x.len()
        invariant
            i <= x.len(),
            result.len() == i,
        decreases x.len() - i
    {
        let val = x[i];
        let exp_val = exp_f32(val);
        result.push(exp_val);
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}