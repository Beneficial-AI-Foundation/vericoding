// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): Add decreases clause to while loop */
fn legweight_helper(x: Vec<f32>) -> (result: Vec<f32>)
    ensures 
        result.len() == x.len(),
        forall|i: int| 0 <= i < result.len() ==> result[i] == 1.0f32
{
    let mut result = Vec::new();
    let mut j: usize = 0;
    while j < x.len()
        invariant
            j <= x.len(),
            result.len() == j,
            forall|k: int| 0 <= k < j ==> result@[k] == 1.0f32
        decreases x.len() - j
    {
        result.push(1.0f32);
        j = j + 1;
    }
    result
}
// </vc-helpers>

// <vc-spec>
fn legweight(x: Vec<f32>) -> (result: Vec<f32>)
    ensures 
        result.len() == x.len(),
        forall|i: int| 0 <= i < result.len() ==> result[i] == 1.0f32
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 3): Add decreases clause to while loop */
{
    let mut result = Vec::new();
    let mut j: usize = 0;
    while j < x.len()
        invariant
            j <= x.len(),
            result.len() == j,
            forall|k: int| 0 <= k < j ==> result@[k] == 1.0f32
        decreases x.len() - j
    {
        result.push(1.0f32);
        j = j + 1;
    }
    result
}
// </vc-code>

}
fn main() {}