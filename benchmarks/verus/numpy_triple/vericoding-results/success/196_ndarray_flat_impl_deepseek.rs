// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): removed ghost parameter and fixed sequence construction */
fn numpy_flat_ghost(a: Vec<f32>) -> (result: Vec<f32>)
    ensures
        result.len() == a.len(),
        forall|i: int| 0 <= i < a.len() ==> result@[i] == a[i]
{
    let mut result = Vec::new();
    let mut idx = 0;
    while idx < a.len()
        invariant
            0 <= idx <= a.len(),
            result.len() == idx,
            forall|i: int| 0 <= i < idx ==> result@[i] == a[i]
        decreases a.len() - idx
    {
        result.push(a[idx]);
        idx = idx + 1;
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
/* code modified by LLM (iteration 4): simplified to call helper without ghost sequence */
{
    numpy_flat_ghost(a)
}
// </vc-code>

}
fn main() {}