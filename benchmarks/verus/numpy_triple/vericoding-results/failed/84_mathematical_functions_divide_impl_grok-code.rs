// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn numpy_divide(x1: Vec<f32>, x2: Vec<f32>) -> (result: Vec<f32>)
    requires 
        x1.len() == x2.len(),
    ensures 
        result.len() == x1.len(),
        forall|i: int| 0 <= i < x1.len() ==> x2[i] != 0.0f32,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Fixed compilation errors by adjusting variable types and using sequence operations consistently to resolve type mismatches with vector indexing and lengths. */
    let mut result = Vec::with_capacity(x1.len());
    let mut i: nat = 0;
    while i < x1@.len()
        invariant
            0nat <= i <= x1@.len(),
            x1@.len() == x2@.len(),
            result@.len() == i,
        decreases x1@.len() - i
    {
        proof { assert(i < x1@.len()); assert(i < x2@.len()); assert(x2@[i] != 0.0f32); }
        let val = x1@[i] / x2@[i];
        result.push(val);
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}