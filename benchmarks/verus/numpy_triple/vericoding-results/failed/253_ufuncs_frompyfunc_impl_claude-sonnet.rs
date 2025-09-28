// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): add spec function wrapper for function application */
spec fn apply_func(func: spec_fn(i8) -> i8, value: i8) -> i8 {
    func(value)
}
// </vc-helpers>

// <vc-spec>
fn numpy_frompyfunc(func: spec_fn(i8) -> i8, input: Vec<i8>) -> (result: Vec<i8>)
    ensures
        result.len() == input.len(),
        forall|i: int| 0 <= i < input.len() ==> result[i] == func(input[i])
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): use helper function for spec function application */
    let mut result = Vec::with_capacity(input.len());
    let mut i = 0;
    while i < input.len()
        invariant
            i <= input.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result[j] == func(input[j])
        decreases input.len() - i
    {
        let value = apply_func(func, input[i]);
        result.push(value);
        i += 1;
    }
    result
}
// </vc-code>

}
fn main() {}