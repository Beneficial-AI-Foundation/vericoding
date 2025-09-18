// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): convert spec function to exec function by removing spec_fn */
fn numpy_frompyfunc_helper<A, B>(func: fn(A) -> B, input: Vec<A>, i: usize) -> (result: B)
    requires
        i < input.len(),
    ensures
        result == func(input@[i as int])
{
    func(input[i])
}
// </vc-helpers>

// <vc-spec>
fn numpy_frompyfunc<A, B>(func: spec_fn(A) -> B, input: Vec<A>) -> (result: Vec<B>)
    ensures
        result.len() == input.len(),
        forall|i: int| 0 <= i < input.len() ==> result[i] == func(input[i])
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): update function parameter and call to match exec function */
{
    let mut result = Vec::new();
    let len = input.len();
    for i in 0..len
        invariant
            result.len() == i as int,
            forall|j: int| 0 <= j < i as int ==> result@[j] == func(input@[j])
    {
        result.push(numpy_frompyfunc_helper(func, input, i));
    }
    result
}
// </vc-code>

}
fn main() {}