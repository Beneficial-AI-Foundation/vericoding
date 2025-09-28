// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn numpy_argwhere(a: Vec<f64>) -> (indices: Vec<usize>)
    ensures

        forall|i: int| 0 <= i < indices@.len() ==> 
            indices@[i] < a@.len() && a@[indices@[i] as int] != 0.0,

        forall|i: int| 0 <= i < a@.len() && a@[i] != 0.0 ==> 
            indices@.contains(i as usize),

        forall|i: int, j: int| 0 <= i < j < indices@.len() ==> 
            indices@[i] != indices@[j],

        forall|i: int, j: int| 0 <= i < j < indices@.len() ==> 
            indices@[i] < indices@[j],
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Fixed value moved error by using ghost variable */
    let mut indices: Vec<usize> = Vec::new();
    let mut i: usize = 0;
    while i < a.len()
        invariant
            i <= a.len(),
            forall|j: int| 0 <= j < indices@.len() ==> 
                indices@[j] < a@.len() && a@[indices@[j] as int] != 0.0,
            forall|j: int| 0 <= j < i && a@[j] != 0.0 ==> 
                indices@.contains(j as usize),
            forall|j: int, k: int| 0 <= j < k < indices@.len() ==> 
                indices@[j] != indices@[k],
            forall|j: int, k: int| 0 <= j < k < indices@.len() ==> 
                indices@[j] < indices@[k],
            forall|j: int| 0 <= j < indices@.len() ==> indices@[j] < i,
        decreases a.len() - i
    {
        if a[i] != 0.0 {
            let ghost old_indices = indices@;
            indices.push(i);
            assert(indices@.len() == old_indices.len() + 1);
            assert(indices@[indices@.len() - 1] == i);
            assert(forall|j: int| 0 <= j < old_indices.len() ==> indices@[j] == old_indices[j]);
        }
        i = i + 1;
    }
    indices
}
// </vc-code>

}
fn main() {}