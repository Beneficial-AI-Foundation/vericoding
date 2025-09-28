// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
#[verifier(external_body)]
fn compute_exp2_f32(x: f32) -> f32 {
    x.exp2()
}
// </vc-helpers>

// <vc-spec>
fn exp2(x: Vec<f32>) -> (result: Vec<f32>)
    ensures
        result.len() == x.len(),
// </vc-spec>
// <vc-code>
{
    let mut result = Vec::new();
    let mut i: usize = 0;
    while i < x.len()
        invariant
            i <= x.len(),
            result.len() == i,
        decreases x.len() - i
    {
        let val = x[i];
        let exp_val = compute_exp2_f32(val);
        result.push(exp_val);
        i = i + 1;
    }
    result
}
// </vc-code>


}
fn main() {}