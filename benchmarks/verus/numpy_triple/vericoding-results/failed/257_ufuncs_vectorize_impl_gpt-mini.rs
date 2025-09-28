// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): helper constructor for Vec */
fn new_vec<B>() -> Vec<B> {
    Vec::new()
}

/* helper modified by LLM (iteration 5): helper to push an element and return the Vec */
fn push_elem<A>(v0: Vec<A>, x: A) -> Vec<A> {
    let mut v = v0;
    v.push(x);
    v
}
// </vc-helpers>

// <vc-spec>
fn vectorize<A, B>(f: spec_fn(A) -> B, arr: Vec<A>) -> (result: Vec<B>)
    ensures
        result.len() == arr.len(),
        forall|i: int| 0 <= i < arr.len() ==> result[i] == f(arr[i])
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): iterate with int index and proper casts */
    let mut res: Vec<B> = new_vec();
    let mut i: int = 0;
    while i < arr.len() as int
        invariant
            res.len() == (i as usize),
            0 <= i,
            i <= arr.len() as int,
            forall|j: int| 0 <= j && j < i ==> res[j] == f(arr[j]),
        decreases arr.len() as int - i
    {
        let a: A = arr[i];
        let b: B = f(a);
        res.push(b);
        i = i + 1;
    }
    res
}
// </vc-code>

}
fn main() {}