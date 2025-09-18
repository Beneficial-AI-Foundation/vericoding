// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn legweight(x: Vec<f32>) -> (result: Vec<f32>)
    ensures 
        result.len() == x.len(),
        forall|i: int| 0 <= i < result.len() ==> result[i] == 1.0f32
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fix loop invariant to match postcondition */
    let mut result = Vec::with_capacity(x.len());
    let mut i: usize = 0;
    while i < x.len()
        invariant
            result.len() == i,
            i <= x.len(),
            forall|j: int| 0 <= j < result.len() ==> result[j] == 1.0f32
        decreases x.len() - i
    {
        result.push(1.0f32);
        i += 1;
    }
    result
}
// </vc-code>

}
fn main() {}