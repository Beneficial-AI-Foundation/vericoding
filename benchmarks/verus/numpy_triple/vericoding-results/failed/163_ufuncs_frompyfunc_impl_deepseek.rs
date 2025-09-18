// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Fix indexing types and remove implementation from helpers */
fn numpy_frompyfunc_helper<A, B>(func: spec_fn(A) -> B, input: Vec<A>) -> (result: Vec<B>)
    ensures
        result.len() == input.len(),
        forall|i: int| 0 <= i < input.len() ==> result[i] == func(input[i]);
// </vc-helpers>

// <vc-spec>
fn numpy_frompyfunc<A, B>(func: spec_fn(A) -> B, input: Vec<A>) -> (result: Vec<B>)
    ensures
        result.len() == input.len(),
        forall|i: int| 0 <= i < input.len() ==> result[i] == func(input[i])
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Implement main function with proper indexing */
    let mut result = Vec::new();
    let mut index: usize = 0;
    let n = input.len();
    while index < n
        invariant
            0 <= index <= n,
            result.len() == index,
            forall|i: int| 0 <= i < index ==> result[i] == func(input[i])
        decreases n - index
    {
        proof {
            assert(input[index] == input@[index as int]);
        }
        result.push(func(input[index]));
        index += 1;
    }
    result
}
// </vc-code>

}
fn main() {}