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
    let mut result = Vec::new();
    let mut i = 0;
    while i < input.len()
        invariant
            0 <= i <= input.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result[j] == func(input[j])
    {
        result.push(func(input[i]));
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}