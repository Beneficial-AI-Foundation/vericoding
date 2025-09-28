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
    /* code modified by LLM (iteration 5): fixed compilation error and added assertion */
    let mut indices: Vec<usize> = Vec::new();
    let mut i: usize = 0;
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            forall|k: int| 0 <= k < indices.len() ==> 
                indices@[k] < i && a[indices@[k] as int] != 0.0f32,
            forall|j: int| 0 <= j < i ==> (a[j] != 0.0f32 <==> 
                (exists|k: int| 0 <= k < indices.len() && indices@[k] as int == j)),
            forall|i1: int, i2: int| 0 <= i1 < i2 < indices.len() ==> indices@[i1] < indices@[i2],
        decreases a.len() - i
    {
        if a[i] != 0.0f32 {
            let old_indices = indices.view();
            indices.push(i);
            proof {
                assert forall|i1: int, i2: int| 0 <= i1 < i2 < indices.len()
                implies indices@[i1] < indices@[i2] by {
                    if i2 < old_indices.len() {
                        assert(old_indices@[i1] < old_indices@[i2]);
                    } else {
                        assert(i2 == old_indices.len());
                        assert(old_indices@[i1] < i);
                        assert(indices@[i2] == i);
                    }
                }

                let k_witness = old_indices.len();
                assert(indices@[k_witness] as int == i);
                assert(exists|k: int| 0 <= k < indices.len() && indices@[k] as int == i);
            }
        } else {
            proof {
                assert forall|k: int| 0 <= k < indices.len() implies indices@[k] as int != i by {
                    assert(indices@[k] < i);
                }
                assert(!(exists|k: int| 0 <= k < indices.len() && indices@[k] as int == i));
            }
        }
        i = i + 1;
    }
    indices
}
// </vc-code>

}
fn main() {}