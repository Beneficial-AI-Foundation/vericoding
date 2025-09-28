// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): removed external_body to avoid verification bypass */
fn reciprocal_single(val: f32) -> (result: f32)
    requires val != 0.0f32,
{
    1.0f32 / val
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
    /* code modified by LLM (iteration 5): fixed type casting for sequence indexing */
    let mut result = Vec::new();
    let mut i = 0;
    
    while i < x.len()
        invariant
            0 <= i <= x.len(),
            result@.len() == i,
        decreases x.len() - i,
    {
        proof {
            assert(0 <= i < x@.len());
            assert(x@[i as int] != 0.0f32);
        }
        let reciprocal = reciprocal_single(x[i]);
        result.push(reciprocal);
        i += 1;
    }
    
    result
}
// </vc-code>

}
fn main() {}