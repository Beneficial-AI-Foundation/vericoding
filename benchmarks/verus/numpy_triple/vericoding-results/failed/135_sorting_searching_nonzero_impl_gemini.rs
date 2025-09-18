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
    /* code modified by LLM (iteration 4): fixed compilation error in sequence equality assertion */
    let mut indices: Vec<usize> = Vec::new();
    let mut i: usize = 0;
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            forall|k: int| 0 <= k < indices.len() ==> (indices[k] < i && a[indices[k] as int] != 0.0f32),
            forall|j: int| 0 <= j < i ==> (a[j] != 0.0f32 <==> (exists|k: int| 0 <= k < indices.len() && indices[k] == j)),
            forall|i1: int, i2: int| 0 <= i1 < i2 < indices.len() ==> indices[i1] < indices[i2],
            forall|k1: int, k2: int| 0 <= k1 < k2 < indices.len() ==> indices[k1] != indices[k2],
        decreases a.len() - i
    {
        if a[i] != 0.0f32 {
            let old_indices = indices@;
            indices.push(i);
            assert(indices@ == old_indices.push(i));
        }
        i = i + 1;
    }
    indices
}
// </vc-code>

}
fn main() {}