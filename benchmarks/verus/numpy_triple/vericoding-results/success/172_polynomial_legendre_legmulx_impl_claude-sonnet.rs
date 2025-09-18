// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn legmulx(c: Vec<f32>) -> (result: Vec<f32>)
    requires c.len() > 0,
    ensures
        result.len() == c.len() + 1,
        result[0] == 0.0f32,
        result[1] == c[0],
        true, // Polynomial coefficients exist (simplified)
// </vc-spec>
// <vc-code>
{
    let mut result = Vec::new();
    result.push(0.0f32);
    for i in 0..c.len()
        invariant
            result.len() == i + 1,
            result.len() <= c.len() + 1,
            result[0] == 0.0f32,
            forall|j: int| 0 <= j < i ==> result[j + 1] == c[j]
    {
        result.push(c[i]);
    }
    result
}
// </vc-code>

}
fn main() {}