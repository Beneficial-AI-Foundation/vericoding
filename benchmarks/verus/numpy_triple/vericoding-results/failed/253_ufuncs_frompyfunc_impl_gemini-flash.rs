// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): removed helper, as it is not needed */
// </vc-helpers>

// <vc-spec>
fn numpy_frompyfunc(func: spec_fn(i8) -> i8, input: Vec<i8>) -> (result: Vec<i8>)
    ensures
        result.len() == input.len(),
        forall|i: int| 0 <= i < input.len() ==> result[i] == func(input[i])
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Removed redundant `old(func.requires(...))` from invariant. */
{
    let mut result: Vec<i8> = Vec::new();
    let mut i: usize = 0;

    while i < input.len()
        invariant
            0 <= i as int && i as int <= input.len() as int,
            result.len() == i,
            forall|j: int| 0 <= j && j < i as int ==> result[j] == func(input[j]),
            input.len() == old(input.len()),
            // func.requires(old(func_arg): (i8,)) == old(func.requires(old(func_arg): (i8,))), // Fix for func == old(func) with old()

        decreases input.len() - i
    {
        let val = input[i];
        result.push(func(val));
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}