// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
proof fn lemma_vec_indexing<T>(v: Vec<T>, i: int)
    requires
        0 <= i < v.len(),
    ensures
        v@[i] == v[i],
{
    // The @ operator for Vec<T> is defined to match indexing
}

proof fn lemma_vec_len<T>(v: Vec<T>)
    ensures
        v.len() == v@.len(),
{
    // The length of the vector matches the length of its ghost sequence
}
// </vc-helpers>

// <vc-spec>
fn reshape(a: Vec<f32>) -> (result: Vec<f32>)
    requires a.len() > 0,
    ensures 
        result.len() == a.len(),
        forall|i: int| 0 <= i < result.len() ==> result[i] == a[i]
// </vc-spec>
// <vc-code>
{
    use std::ops::Index;
    /* code modified by LLM (iteration 3): Removed duplicate lemma usage, kept trait import */
    let result = a;
    result
}
// </vc-code>

}
fn main() {}