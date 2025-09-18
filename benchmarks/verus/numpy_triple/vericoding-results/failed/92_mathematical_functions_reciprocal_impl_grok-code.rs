// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn numpy_reciprocal(x: Vec<f32>) -> (result: Vec<f32>)
    requires 
        x.len() > 0,
        forall|i: int| 0 <= i < x.len() ==> x[i] != 0.0_f32,
    ensures
        result.len() == x.len(),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Fixed compilation error by adding proper function braces and implemented reciprocal calculation with proof assertions for bounds and non-zero values. */
    let mut result = Vec::new();
    let len = x.len();
    for k in 0..len {
        proof {
            assert(0 <= k as int < x.len());
            assert(x[k] != 0.0_f32);
        }
        let xi_exe = x[k];
        result.push(1.0_f32 / xi_exe);
    }
    result
}
// </vc-code>

}
fn main() {}