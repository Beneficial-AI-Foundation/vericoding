// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Added helper lemma to prove invariant preservation */
lemma lemma_indices_monotonic(indices: &Vec<usize>, new_index: usize)
    requires
        forall|i1: int, i2: int| 0 <= i1 < i2 < indices.len() ==> indices[i1] < indices[i2],
        indices.len() > 0 ==> indices[indices.len() - 1] < new_index,
    ensures
        forall|i1: int, i2: int| 0 <= i1 < i2 < indices.len() + 1 ==> 
            if i2 == indices.len() { indices[i1] < new_index }
            else { indices[i1] < indices[i2] },
{}
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
    /* code modified by LLM (iteration 5): Added proof blocks to establish invariants after push */
    let mut indices: Vec<usize> = Vec::new();
    let mut i: usize = 0;
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            forall|k: int| 0 <= k < indices.len() ==> (indices[k] < a.len() && a[indices[k] as int] != 0.0f32),
            forall|j: int| 0 <= j < i ==> (a[j] != 0.0f32 <==> exists|k: int| 0 <= k < indices.len() && indices[k] == j),
            forall|i1: int, i2: int| 0 <= i1 < i2 < indices.len() ==> indices[i1] < indices[i2],
        decreases a.len() - i
    {
        if a[i] != 0.0f32 {
            proof {
                if indices.len() > 0 {
                    lemma_indices_monotonic(&indices, i);
                }
            }
            indices.push(i);
        }
        i += 1;
    }
    indices
}
// </vc-code>

}
fn main() {}