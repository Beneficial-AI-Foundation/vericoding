// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Added a helper function to convert int to usize */
fn int_to_usize(i: int) -> usize
    requires i >= 0
    ensures (i as usize) as int == i
{
    i as usize
}
// </vc-helpers>

// <vc-spec>
fn numpy_frompyfunc<A, B>(func: spec_fn(A) -> B, input: Vec<A>) -> (result: Vec<B>)
    ensures
        result.len() == input.len(),
        forall|i: int| 0 <= i < input.len() ==> result[i] == func(input[i])
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Corrected type handling for `i` and indexing. */
{
    let mut result = Vec::new();
    result.reserve(input.len());
    let mut i: usize = 0;
    while i < input.len()
        invariant
            0 <= i as int,
            i as int <= input.len() as int,
            result.len() == i,
            forall|j: int| 0 <= j < i as int ==> result@[j] == func(input@[j as usize])
    {
        result.push(func(input@[i]));
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}