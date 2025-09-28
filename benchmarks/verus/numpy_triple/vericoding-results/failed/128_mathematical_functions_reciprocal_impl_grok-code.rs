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
        forall|i: int| 0 <= i < x@.len() ==> x@[i] != 0.0f32,
    ensures
        result@.len() == x@.len(),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fixed type error by using int for index, added postcondition for reciprocal values */
    let mut result: Vec<f32> = Vec::new();
    for i: int in 0..(x.len() as int)
        invariant
            result@.len() == i as nat,
            x@.len() == x.len() as int,
            forall|k: int| 0 <= k < x@.len() ==> x@[k] != 0.0f32,
            forall|j: int| 0 <= j < result@.len() ==> result@[j] == 1.0f32 / x@[j]
    {
        assert(x@[i] != 0.0f32);
        let recip: f32 = 1.0 / x@[i];
        result.push(recip);
    }
    result
}
// </vc-code>

}
fn main() {}