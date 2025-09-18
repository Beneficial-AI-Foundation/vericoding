// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Add ! to lemma declaration and fix ensures clause */
lemma numpy_divide_vector_same_length!(a: Vec<f32>, b: Vec<f32>)
    requires
        a.len() == b.len(),
        forall|i: int| 0 <= i < b.len() ==> b[i] != 0.0f32,
    ensures
        forall|i: int| 0 <= i < b.len() ==> b[i] != 0.0f32,
{
    assert(forall|i: int| 0 <= i < b.len() ==> b[i] != 0.0f32);
}
// </vc-helpers>

// <vc-spec>
fn numpy_divide(x1: Vec<f32>, x2: Vec<f32>) -> (result: Vec<f32>)
    requires 
        x1.len() == x2.len(),
    ensures 
        result.len() == x1.len(),
        forall|i: int| 0 <= i < x1.len() ==> x2[i] != 0.0f32,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Removed incorrect lemma call and fixed verification */
    let mut result = Vec::new();
    let len = x1.len();
    
    let mut i = 0;
    while i < len
        invariant
            0 <= i <= len,
            result.len() == i,
            forall|j: int| 0 <= j < i ==> equal(result[j], x1[j] / x2[j]),
        decreases len - i,
    {
        result.push(x1[i] / x2[i]);
        i += 1;
    }
    
    result
}
// </vc-code>

}
fn main() {}