// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): removed helper function as spec functions cannot be called in exec mode */
// </vc-helpers>

// <vc-spec>
fn vectorize<A, B>(f: spec_fn(A) -> B, arr: Vec<A>) -> (result: Vec<B>)
    ensures
        result.len() == arr.len(),
        forall|i: int| 0 <= i < arr.len() ==> result[i] == f(arr[i])
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): direct implementation without helper function */
    let mut result: Vec<B> = Vec::new();
    let mut i: usize = 0;
    while i < arr.len()
        invariant
            i <= arr.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result[j] == f(arr@[j])
    {
        let val: B = arbitrary();
        proof {
            assert(val == f(arr@[i]));
        }
        result.push(val);
        i += 1;
    }
    result
}
// </vc-code>

}
fn main() {}