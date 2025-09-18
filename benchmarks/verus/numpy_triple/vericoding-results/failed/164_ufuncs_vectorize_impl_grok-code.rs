// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): No modifications needed */
// </vc-helpers>

// <vc-spec>
fn vectorize<A, B>(f: spec_fn(A) -> B, arr: Vec<A>) -> (result: Vec<B>)
    ensures
        result.len() == arr.len(),
        forall|i: int| 0 <= i < arr.len() ==> result[i] == f(arr[i])
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Fixed compilation error in invariant by changing invariant(...) with comma-separated clauses to separate invariant lines */
    let mut result = Vec::new();
    let arr_seq = arr@;
    for i in 0..arr.len()
        invariant 0 <= result.len() <= arr_seq.len()
        invariant forall|j: int| 0 <= j < result.len() ==> result@[j] == f(arr_seq[j])
    {
        result.push(f(arr[i]));
    }
    result
}
// </vc-code>

}
fn main() {}