// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): No helpers are needed for this function. */
// </vc-helpers>

// <vc-spec>
fn nonzero(a: Vec<f32>) -> (indices: Vec<usize>)
    ensures
        forall|i: int| 0 <= i < indices.len() ==> (indices[i] < a.len() && a[indices[i] as int] != 0.0f32),
        forall|j: int| 0 <= j < a.len() ==> (a[j] != 0.0f32 <==> exists|k: int| 0 <= k < indices.len() && indices[k] == j),
        forall|i1: int, i2: int| 0 <= i1 < i2 < indices.len() ==> indices[i1] < indices[i2],
        forall|i: int, j: int| 0 <= i < j < indices.len() ==> indices[i] != indices[j],
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Fixed type errors and `vec_index` to `index`. Replaced `i` with `i as usize` for array indexing. */
    let mut indices: Vec<usize> = Vec::new();
    let mut i: usize = 0;
    while i < a.len()
        invariant
            0 <= i as int,
            i as int <= a.len() as int,
            forall|idx: int| 0 <= idx < indices.len() ==> (indices[idx] < i && a[indices[idx] as int] != 0.0f32),
            forall|j: int| 0 <= j < i ==> (a[j as usize] != 0.0f32 <==> exists|k: int| 0 <= k < indices.len() && indices[k] == j),
            forall|i1: int, i2: int| 0 <= i1 < i2 < indices.len() ==> indices[i1] < indices[i2],
            forall|i_idx: int, j_idx: int| 0 <= i_idx < j_idx < indices.len() ==> indices[i_idx] != indices[j_idx],
            indices.len() <= a.len(),
    {
        if a[i] != 0.0f32 {
            indices.push(i);
        }
        i = i + 1;
    }
    indices
}
// </vc-code>

}
fn main() {}