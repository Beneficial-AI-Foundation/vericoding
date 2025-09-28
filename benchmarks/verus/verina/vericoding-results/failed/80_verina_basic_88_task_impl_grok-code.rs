// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Spec helper to convert Seq to Vec avoiding exec ghost access */
spec fn to_array_impl(xs: &Seq<i32>) -> Vec<i32>
    ensures
        result.len() == xs.len(),
        forall|i: int| 0 <= i < xs.len() ==> result[i] == xs[i]
{
    let mut result = Vec::new();
    let len = xs.len();
    for i in 0..len {
        result.push(xs[i]);
    }
    result
}
// </vc-helpers>

// <vc-spec>
fn to_array(xs: &Seq<i32>) -> (result: Vec<i32>)
    ensures
        result.len() == xs.len(),
        forall|i: int| 0 <= i < xs.len() ==> result[i] == xs[i],
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Call spec helper to construct Vec */
    to_array_impl(xs)
}
// </vc-code>

}
fn main() {}