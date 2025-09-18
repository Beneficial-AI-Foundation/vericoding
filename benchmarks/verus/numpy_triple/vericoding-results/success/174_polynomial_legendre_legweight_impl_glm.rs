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
    /* code modified by LLM (iteration 4): added loop invariants to prove postconditions */
    let len = x.len();
    let mut result = Vec::new();
    for i in 0..len
        invariant 
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result[j] == 1.0f32
    {
        result.push(1.0f32);
    }
    result
}
// </vc-code>

}
fn main() {}