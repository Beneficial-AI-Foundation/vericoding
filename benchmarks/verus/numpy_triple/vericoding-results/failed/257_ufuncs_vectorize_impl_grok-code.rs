// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn vectorize<A, B>(f: spec_fn(A) -> B, arr: Vec<A>) -> (result: Vec<B>)
    ensures
        result.len() == arr.len(),
        forall|i: int| 0 <= i < arr.len() ==> result[i] == f(arr[i])
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fix ghost let to let ghost for compilation */
    let mut result = Vec::with_capacity(arr.len());
    let mut i: usize = 0;
    let len = arr.len();
    while i < len
        invariant
            result.len() == i as int,
            forall|j: int| 0 <= j < i as int ==> result@[j] == f(arr@[j])
        decreases len - i as int
    {
        let ghost i_int: int = i as int;
        result.push(f(arr@[i_int]));
        i += 1;
    }
    result
}
// </vc-code>

}
fn main() {}