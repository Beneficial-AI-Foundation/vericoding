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
/* code modified by LLM (iteration 5): fixed loop invariant syntax by combining invariants and removing redundant bounds */
{
    let mut result = Vec::new();
    let n = x.len();
    for i in 0..n
        invariant i <= n && result.len() == i
    {
        result.push(1.0 / x[i]);
    }
    result
}
// </vc-code>

}
fn main() {}