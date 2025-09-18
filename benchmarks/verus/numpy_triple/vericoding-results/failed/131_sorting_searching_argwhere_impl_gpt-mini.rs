// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): predicate for non-zero check */
spec fn is_nonzero(x: f64) -> bool { x != 0.0 }
// </vc-helpers>

// <vc-spec>
fn numpy_argwhere(a: Vec<f64>) -> (indices: Vec<usize>)
    ensures

        forall|i: int| 0 <= i < indices.len() ==> 
            indices[i] < a.len() && a[indices[i] as int] != 0.0,

        forall|i: int| 0 <= i < a.len() && a[i] != 0.0 ==> 
            indices@.contains(i as usize),

        forall|i: int, j: int| 0 <= i < j < indices.len() ==> 
            indices[i] != indices[j],

        forall|i: int, j: int| 0 <= i < j < indices.len() ==> 
            indices[i] < indices[j],
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): collect indices of non-zero elements preserving order */
    let mut indices: Vec<usize> = Vec::new();
    let mut i: usize = 0;
    while i < a.len()
        invariant i <= a.len()
        invariant forall |k: int| 0 <= k && k < (indices@.len() as int) ==> indices@[k] < a.len()
        invariant forall |k: int| 0 <= k && k < (indices@.len() as int) ==> a@[indices@[k] as int] != 0.0
        invariant forall |k: int, j: int| 0 <= k && k < j && j < (indices@.len() as int) ==> indices@[k] < indices@[j]
        invariant forall |k: int| 0 <= k && k < (indices@.len() as int) ==> (indices@[k] as int) < (i as int)
        decreases (a@.len() as int) - (i as int)
    {
        if a@[i as int] != 0.0 {
            indices.push(i);
        }
        i = i + 1;
    }
    indices
}
// </vc-code>

}
fn main() {}