// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): fixed helper functions to use proper verification syntax */
fn reciprocal_elem(x: f32) -> (result: f32)
    requires x != 0.0f32,
    ensures result == 1.0f32 / x,
{
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
    /* code modified by LLM (iteration 5): fixed implementation with proper verification */
    let mut result = Vec::new();
    let mut i: usize = 0;
    
    while i < x.len()
        invariant
            i >= 0,
            i <= x@.len(),
            result@.len() == i,
            forall|j: int| 0 <= j < i ==> result@[j] == 1.0f32 / x@[j],
        decreases x@.len() - i,
    {
        let elem = x[i];
        let recip = reciprocal_elem(elem);
        result.push(recip);
        i = i + 1;
    }
    proof {
        assert(result@.len() == x@.len());
    }
    result
}
// </vc-code>

}
fn main() {}