// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn legweight(x: Vec<f32>) -> (result: Vec<f32>)
    ensures 
        result@.len() == x@.len(),
        forall|i: int| 0 <= i < result@.len() ==> result@[i] == 1.0f32
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): Added decreases clause to fix verification error */
    let mut result = Vec::new();
    let mut i = 0;
    while i < x.len()
        invariant
            0 <= i <= x.len(),
            result@.len() == i,
            forall|j: int| 0 <= j < i ==> result@[j] == 1.0f32,
        decreases x.len() - i
    {
        result.push(1.0f32);
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}