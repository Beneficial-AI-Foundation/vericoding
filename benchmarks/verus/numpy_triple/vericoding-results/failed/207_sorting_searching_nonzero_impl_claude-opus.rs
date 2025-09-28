// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

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
    /* code modified by LLM (iteration 5): Fixed ownership issue by using ghost variable for proof */
    let mut indices: Vec<usize> = Vec::new();
    let mut i: usize = 0;
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            forall|j: int| 0 <= j < indices.len() ==> (indices[j] < a.len() && a[indices[j] as int] != 0.0f32),
            forall|j: int| 0 <= j < i ==> (a[j] != 0.0f32 <==> exists|k: int| 0 <= k < indices.len() && indices[k] == j),
            forall|i1: int, i2: int| 0 <= i1 < i2 < indices.len() ==> indices[i1] < indices[i2],
            forall|i1: int, j: int| 0 <= i1 < j < indices.len() ==> indices[i1] != indices[j],
            forall|j: int| 0 <= j < indices.len() ==> indices[j] < i,
        decreases a.len() - i
    {
        if a[i] != 0.0f32 {
            let ghost old_indices = indices@;
            indices.push(i);
            proof {
                assert(indices@.len() == old_indices.len() + 1);
                assert(indices@[indices@.len() - 1] == i);
                assert(forall|j: int| 0 <= j < old_indices.len() ==> indices@[j] == old_indices[j]);
                assert(forall|j: int| 0 <= j < indices@.len() - 1 ==> indices@[j] < i);
                assert(indices@[indices@.len() - 1] == i);
                assert(a[i as int] != 0.0f32);
                assert(forall|j: int| 0 <= j < indices@.len() ==> (indices@[j] < a.len() && a[indices@[j] as int] != 0.0f32));
                assert(forall|j: int| 0 <= j <= i ==> (a[j] != 0.0f32 <==> exists|k: int| 0 <= k < indices@.len() && indices@[k] == j));
            }
        }
        i = i + 1;
    }
    indices
}
// </vc-code>

}
fn main() {}