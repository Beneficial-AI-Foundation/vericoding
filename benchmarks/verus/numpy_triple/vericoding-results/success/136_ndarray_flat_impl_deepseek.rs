// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): add decreases clause to while loop */
fn numpy_flat_helper(a: Vec<f32>) -> (result: Vec<f32>)
    ensures
        result.len() == a.len(),
        forall|i: int| 0 <= i < a.len() ==> result[i] == a[i]
{
    let mut result = Vec::new();
    let mut index = 0;
    while index < a.len()
        invariant
            0 <= index <= a.len(),
            result.len() == index,
            forall|i: int| 0 <= i < index ==> result[i] == a[i]
        decreases a.len() - index
    {
        result.push(a[index]);
        index += 1;
    }
    result
}
// </vc-helpers>

// <vc-spec>
fn numpy_flat(a: Vec<f32>) -> (result: Vec<f32>)
    ensures
        result.len() == a.len(),
        forall|i: int| 0 <= i < a.len() ==> result[i] == a[i]
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 3): unchanged, still calls helper function */
{
    numpy_flat_helper(a)
}
// </vc-code>

}
fn main() {}