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
/* code modified by LLM (iteration 4): adding proof assertions inside conditional blocks */
{
    let mut indices: Vec<usize> = Vec::new();
    let mut i: usize = 0;
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            forall|k: int| 0 <= k < indices.len() ==> 
                (indices[k] as int) < i && a[indices[k] as int] != 0.0,
            forall|k: int| 0 <= k < i && a[k] != 0.0 ==> 
                indices@.contains(k as usize),
            forall|k: int, j: int| 0 <= k < j < indices.len() ==> 
                indices[k] < indices[j],
        decreases a.len() - i
    {
        let ghost old_indices = indices@;
        if a[i] != 0.0 {
            indices.push(i);
            proof {
                let next_i = i + 1;
                assert forall|k: int| 0 <= k < indices.len() implies (indices[k] as int) < next_i && a[indices[k] as int] != 0.0 by {
                    if k < old_indices.len() {
                        assert(old_indices[k] < i); 
                    } else {
                        assert(indices[k] == i);
                    }
                }
                assert forall|k: int| 0 <= k < next_i && a[k] != 0.0 implies indices@.contains(k as usize) by {
                    if k < i {
                        assert(old_indices.contains(k as usize));
                        assert(indices@.contains(k as usize));
                    } else {
                        assert(k == i);
                        assert(indices@.contains(i as usize));
                    }
                }
            }
        } else {
            proof {
                assert(indices@ == old_indices);
                let next_i = i + 1;
                assert forall|k: int| 0 <= k < indices.len() implies (indices[k] as int) < next_i by {
                    assert(indices[k] < i);
                }
                assert forall|k: int| 0 <= k < next_i && a[k] != 0.0 implies indices@.contains(k as usize) by {
                    assert(k < i);
                    assert(old_indices.contains(k as usize));
                }
            }
        }
        i = i + 1;
    }
    indices
}
// </vc-code>

}
fn main() {}