// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): provide spec_apply wrapper for spec function */
spec fn spec_apply(func: spec_fn(i8) -> i8, x: i8) -> i8 { func(x) }
// </vc-helpers>

// <vc-spec>
fn numpy_frompyfunc(func: spec_fn(i8) -> i8, input: Vec<i8>) -> (result: Vec<i8>)
    ensures
        result.len() == input.len(),
        forall|i: int| 0 <= i < input.len() ==> result[i] == func(input[i])
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fix quantifier index types in invariant */
    let mut result: Vec<i8> = Vec::new();
    let mut i: usize = 0;
    while i < input.len()
        invariant
            i <= input.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i as int ==> result[j] == func(input[j]),
        decreases input.len() - i
    {
        let v: i8 = input[i];
        let y: i8 = func(v);
        result.push(y);
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}