// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): return input vector */
fn clone_vec_f32(a: Vec<f32>) -> (result: Vec<f32>)
    ensures
        result.len() == a.len(),
        forall|i: int| 0 <= i < a.len() ==> result[i] == a[i],
{
    let result = a;
    result
}
// </vc-helpers>

// <vc-spec>
fn asanyarray(a: Vec<f32>) -> (result: Vec<f32>)
    ensures
        result.len() == a.len(),
        forall|i: int| 0 <= i < a.len() ==> result[i] == a[i],
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): call helper to clone vector */
    let result = clone_vec_f32(a);
    result
}
// </vc-code>

}
fn main() {}