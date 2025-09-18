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
    /* code modified by LLM (iteration 5): fixed invariants to properly maintain loop conditions */
    let mut indices: Vec<usize> = Vec::new();
    let mut i = 0;
    
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            forall|idx: int| 0 <= idx < indices.len() ==> (indices[idx] < a.len() && a[indices[idx] as int] != 0.0f32),
            forall|j: int| 0 <= j < i ==> (a[j] != 0.0f32 <==> exists|k: int| 0 <= k < indices.len() && indices[k] == j),
            forall|i1: int, i2: int| 0 <= i1 < i2 < indices.len() ==> indices[i1] < indices[i2],
        decreases a.len() - i
    {
        if a[i] != 0.0f32 {
            proof {
                assert(i < a.len());
                assert(a[i as int] != 0.0f32);
                assert(forall|k: int| 0 <= k < indices.len() ==> indices[k] < i);
            }
            indices.push(i);
            proof {
                assert(indices[indices.len() - 1] == i);
                assert(i < a.len());
                assert(a[i as int] != 0.0f32);
            }
        }
        i += 1;
    }
    
    indices
}
// </vc-code>

}
fn main() {}