// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn numpy_frompyfunc(func: spec_fn(i8) -> i8, input: Vec<i8>) -> (result: Vec<i8>)
    ensures
        result.len() == input.len(),
        forall|i: int| 0 <= i < input.len() ==> result[i] == func(input[i])
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): apply func to each element */
    let mut result = Vec::new();
    for i in 0..input.len() {
        let elem = input[i];
        result.push(func(elem));
    }
    result
}
// </vc-code>

}
fn main() {}