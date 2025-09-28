// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Fix argument types for helper lemmas */
fn is_zero(x: f64) -> bool { x == 0.0 }

proof fn lemma_vec_contains_nonnzero_indices(a: Seq<f64>, indices: Seq<usize>, k: int)
    requires
        0 <= k <= a.len(),
        forall|i: int| 0 <= i < indices.len() ==> indices[i] < k as int && a[indices[i] as int] != 0.0,
        forall|i: int| 0 <= i < k && a[i] != 0.0 ==> indices.contains(i as usize)
{
}

proof fn lemma_index_ordering_unique(indices: Seq<usize>)
    requires
        forall|i: int, j: int| 0 <= i < j < indices.len() ==> indices[i] != indices[j],
        forall|i: int, j: int| 0 <= i < j < indices.len() ==> indices[i] < indices[j]
{
}
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
    /* code modified by LLM (iteration 5): Fix integer conversion for lemma call */
    let mut indices_vec: Vec<usize> = Vec::new();
    let mut idx: usize = 0;
    
    while idx < a.len()
        invariant
            idx <= a@.len(),
            indices_vec@.len() <= a@.len(),
            forall|i: int| 0 <= i < indices_vec@.len() ==> indices_vec@[i] < idx as int && a@[indices_vec@[i] as int] != 0.0,
            forall|i: int| 0 <= i < idx as int && a@[i] != 0.0 ==> indices_vec@.contains(i as usize),
            forall|i: int, j: int| 0 <= i < j < indices_vec@.len() ==> indices_vec@[i] != indices_vec@[j],
            forall|i: int, j: int| 0 <= i < j < indices_vec@.len() ==> indices_vec@[i] < indices_vec@[j]
        decreases a.len() - idx
    {
        if !is_zero(a[idx]) {
            indices_vec.push(idx);
            proof {
                lemma_index_ordering_unique(indices_vec@);
            }
        }
        idx += 1;
        proof {
            lemma_vec_contains_nonnzero_indices(a@, indices_vec@, idx as int);
        }
    }
    
    indices_vec
}
// </vc-code>

}
fn main() {}