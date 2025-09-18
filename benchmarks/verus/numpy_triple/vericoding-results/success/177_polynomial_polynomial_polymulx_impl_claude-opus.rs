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
    /* code modified by LLM (iteration 2): Added decreases clause to fix loop verification */
    let mut result = Vec::new();
    result.push(0.0f32);
    let mut i = 0;
    while i < c.len()
        invariant
            i <= c.len(),
            result.len() == i + 1,
            result[0] == 0.0f32,
            forall|j: int| 0 <= j < i ==> result[j + 1] == c[j],
        decreases c.len() - i
    {
        result.push(c[i]);
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}