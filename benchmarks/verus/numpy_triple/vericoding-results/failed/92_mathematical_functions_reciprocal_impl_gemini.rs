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
    /* code modified by LLM (iteration 5): introduced an intermediate variable to help prove the division precondition */
    let mut result = Vec::new();
    let mut i: usize = 0;
    while i < x.len()
        invariant
            0 <= i <= x.len(),
            result.len() == i,
            forall|j: int| 0 <= j < x.len() ==> x@[j] != 0.0_f32,
        decreases x.len() - i
    {
        let val = x[i];
        assert(val != 0.0_f32);
        let reciprocal = 1.0_f32 / val;
        result.push(reciprocal);
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}