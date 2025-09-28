// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
use std::ops::Index;
/* helper modified by LLM (iteration 5): added import of Index trait to resolve compilation errors */
fn vectorize_inner<A, B>(f: spec_fn(A) -> B, arr: Vec<A>, start: usize, result: &mut Vec<B>)
    requires
        start <= arr.len(),
        result.len() == start,
        forall|j: int| 0 <= j < start as int ==> result@[j] == f(arr.index(j))
    ensures
        result.len() == arr.len(),
        forall|j: int| 0 <= j < arr.len() ==> result@[j] == f(arr.index(j))
{
    let mut i = start;
    while i < arr.len()
        invariant
            i >= start,
            i <= arr.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i as int ==> result@[j] == f(arr.index(j))
        decreases arr.len() - i
    {
        result.push(f(arr.index(i)));
        i = i + 1;
    }
}
// </vc-helpers>

// <vc-spec>
fn vectorize<A, B>(f: spec_fn(A) -> B, arr: Vec<A>) -> (result: Vec<B>)
    ensures
        result.len() == arr.len(),
        forall|i: int| 0 <= i < arr.len() ==> result[i] == f(arr[i])
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): no changes needed in this iteration */
{
    let mut result = Vec::new();
    vectorize_inner(f, arr, 0, &mut result);
    result
}
// </vc-code>

}
fn main() {}