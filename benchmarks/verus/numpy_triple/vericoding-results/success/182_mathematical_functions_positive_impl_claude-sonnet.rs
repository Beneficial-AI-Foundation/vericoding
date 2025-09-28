// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// Helper function to check if a float is positive
fn is_positive(x: f32) -> bool {
    x > 0.0
}
// </vc-helpers>

// <vc-spec>
fn positive(x: Vec<f32>) -> (result: Vec<f32>)
    ensures
        result.len() == x.len(),
        forall|i: int| 0 <= i < result.len() ==> result[i] == x[i],
// </vc-spec>
// <vc-code>
{
    let mut result: Vec<f32> = Vec::new();
    let mut i = 0;
    
    while i < x.len()
        invariant
            i <= x.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result[j] == x[j],
        decreases x.len() - i
    {
        result.push(x[i]);
        i += 1;
    }
    
    result
}
// </vc-code>

}
fn main() {}