// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): fix proof function call by adding proof block */
proof fn decreases_lemma(a: &Vec<f64>, i: usize)
    ensures
        (a.len() as int - i as int) >= 0,
{
}

proof fn preserves_invariants(a: &Vec<f64>, indices: &Vec<usize>, i: usize)
    ensures
        i <= a.len(),
        forall|k: int| 0 <= k < indices.len() ==> indices[k] < a.len(),
        forall|k: int| 0 <= k < indices.len() ==> a[indices[k] as int] != 0.0,
        forall|k: int| 0 <= k < a.len() && a[k] != 0.0 ==> exists|j: int| 0 <= j < indices.len() && indices[j] == k,
        forall|k: int, l: int| 0 <= k < indices.len() && 0 <= l < indices.len() && k != l ==> indices[k] != indices[l],
        forall|k: int, l: int| 0 <= k < indices.len() && 0 <= l < indices.len() && indices[k] < indices[l] ==> k < l,
{
}
// </vc-helpers>

// <vc-spec>
fn argwhere(a: &Vec<f64>) -> (indices: Vec<usize>)
    ensures
        forall|i: int| 0 <= i < indices.len() ==> (#[trigger] indices[i]) < a.len(),
        forall|i: int| 0 <= i < indices.len() ==> a[indices[i] as int] != 0.0,
        forall|i: int| 0 <= i < a.len() && a[i] != 0.0 ==> exists|j: int| 0 <= j < indices.len() && indices[j] == i,
        forall|i: int, j: int| 0 <= i < indices.len() && 0 <= j < indices.len() && i != j ==> indices[i] != indices[j],
        forall|i: int, j: int| 0 <= i < indices.len() && 0 <= j < indices.len() && (indices[i] as int) < (indices[j] as int) ==> i < j,
        (indices.len() == 0) == (forall|i: int| 0 <= i < a.len() ==> a[i] == 0.0),
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): wrap proof function calls in proof blocks */
{
    let mut indices: Vec<usize> = Vec::new();
    let mut i: usize = 0;
    
    while i < a.len()
        invariant
            i <= a.len(),
            forall|k: int| 0 <= k < indices.len() ==> indices[k] < a.len(),
            forall|k: int| 0 <= k < indices.len() ==> a[indices[k] as int] != 0.0,
            forall|k: int| 0 <= k < a.len() && a[k] != 0.0 ==> exists|j: int| 0 <= j < indices.len() && indices[j] == k,
            forall|k: int, l: int| 0 <= k < indices.len() && 0 <= l < indices.len() && k != l ==> indices[k] != indices[l],
            forall|k: int, l: int| 0 <= k < indices.len() && 0 <= l < indices.len() && indices[k] < indices[l] ==> k < l,
        decreases a.len() - i
    {
        proof {
            decreases_lemma(a, i);
        }
        
        if a[i] != 0.0 {
            indices.push(i);
        }
        i += 1;
        
        proof {
            preserves_invariants(a, &indices, i);
        }
    }
    
    indices
}
// </vc-code>

}
fn main() {}