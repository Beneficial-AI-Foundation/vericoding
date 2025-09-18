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
{ /* code modified by LLM (iteration 5): added `assert` to help prove invariants after `push` */
    let mut indices: Vec<usize> = Vec::new();
    let mut i: usize = 0;
    while i < a.len()
        invariant
            0 <= i as int && i as int <= a.len() as int,
            forall|idx: int| 0 <= idx < indices.len() ==> indices[idx] < i && a[indices[idx] as int] != 0.0,
            // Indices remain sorted and distinct
            forall|idx: int, jdx: int| 0 <= idx < jdx < indices.len() ==> indices[idx] < indices[jdx] && indices[idx] != indices[jdx],
            // All non-zero elements up to i-1 are in the `indices` vector
            forall|k: int| 0 <= k < i as int && a[k as int] != 0.0 ==> indices@.contains(k as usize)
        decreases a.len() - i
    {
        if a[i] != 0.0 {
            let old_indices_len = indices.len();
            indices.push(i);
            assert(indices.len() == old_indices_len + 1);
            assert(indices@[old_indices_len as int] == i);
            assert(indices@[old_indices_len as int] < i + 1);
            assert(a[indices@[old_indices_len as int] as int] != 0.0);
        }
        i = i + 1;
    }
    indices
}
// </vc-code>

}
fn main() {}