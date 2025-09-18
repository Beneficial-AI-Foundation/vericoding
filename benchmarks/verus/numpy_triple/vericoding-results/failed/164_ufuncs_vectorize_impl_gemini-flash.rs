// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Corrected `Seq::singleton` to `Seq::unit` and ensured `arr.len()` is of type `int` for `subrange`. */
spec fn vectorize_spec<A, B>(f: spec_fn(A) -> B, arr: Seq<A>) -> Seq<B> {
    if arr.len() == 0 {
        Seq::empty()
    } else {
        let first = arr.index(0);
        let arr_len_int: int = arr.len() as int;
        let rest = arr.subrange(1, arr_len_int);
        Seq::unit(f(first)).add(vectorize_spec(f, rest))
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
/* code modified by LLM (iteration 5): Added `use std::ops::Index;` to bring the `Index` trait into scope and corrected `arr.index(i)` to `arr[i]` for `Vec` indexing. */
{
    use std::ops::Index;
    let mut result_vec = Vec::new();
    let mut i = 0;
    while i < arr.len()
        invariant
            result_vec.len() == i,
            i <= arr.len(),
            forall|j: int| 0 <= j < i ==> result_vec.view()[j] == f(arr.view()[j])
    {
        let item = arr[i];
        let mapped_item = f(item);
        result_vec.push(mapped_item);
        i = i + 1;
    }
    result_vec
}
// </vc-code>

}
fn main() {}