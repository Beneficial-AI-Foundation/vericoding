// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn polymulx(c: Vec<f32>) -> (result: Vec<f32>)
    ensures
        result.len() == c.len() + 1,
        result[0] == 0.0f32,
        forall|i: int| 0 <= i < c.len() ==> result[i + 1] == c[i],
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): added loop invariant to track vector properties */
    let mut result = Vec::new();
    result.push(0.0f32);
    for i in 0..c.len()
        invariant
            result@[0] == 0.0f32,
            result@.len() == i + 1,
            forall|j: int| 0 <= j < (i as int) ==> result@[j + 1] == c@[j],
    {
        result.push(c[i]);
    }
    result
}
// </vc-code>

}
fn main() {}