// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

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
    /* code modified by LLM (iteration 5): Fixed loop invariants and assertions */
    let mut indices: Vec<usize> = Vec::new();
    let mut i: usize = 0;
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            forall|j: int| 0 <= j < indices.len() ==> indices[j] < a.len() && a[indices[j] as int] != 0.0,
            forall|j: int| 0 <= j < i && a[j] != 0.0 ==> exists|k: int| 0 <= k < indices.len() && indices[k] == j,
            forall|j: int, k: int| 0 <= j < k < indices.len() ==> indices[j] != indices[k],
            forall|j: int, k: int| 0 <= j < k < indices.len() ==> indices[j] < indices[k],
            forall|j: int| 0 <= j < indices.len() ==> indices[j] < i,
        decreases a.len() - i
    {
        if a[i] != 0.0 {
            indices.push(i);
        }
        i = i + 1;
    }
    indices
}
// </vc-code>

}
fn main() {}