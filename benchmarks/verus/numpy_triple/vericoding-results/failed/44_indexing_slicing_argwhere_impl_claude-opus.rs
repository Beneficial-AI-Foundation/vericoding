// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

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
{
    /* code modified by LLM (iteration 5): Fixed old() expression type issue */
    let mut indices: Vec<usize> = Vec::new();
    let mut i: usize = 0;
    while i < a.len()
        invariant
            i <= a.len(),
            forall|k: int| 0 <= k < indices.len() ==> (#[trigger] indices[k]) < a.len(),
            forall|k: int| 0 <= k < indices.len() ==> a[indices[k] as int] != 0.0,
            forall|k: int| 0 <= k < i && a[k] != 0.0 ==> exists|j: int| 0 <= j < indices.len() && indices[j] == k,
            forall|k: int| 0 <= k < a.len() && a[k] != 0.0 && !exists|j: int| 0 <= j < indices.len() && indices[j] == k ==> k >= i,
            forall|k: int, j: int| 0 <= k < indices.len() && 0 <= j < indices.len() && k != j ==> indices[k] != indices[j],
            forall|k: int, j: int| 0 <= k < indices.len() && 0 <= j < indices.len() && (indices[k] as int) < (indices[j] as int) ==> k < j,
            forall|k: int| 0 <= k < indices.len() ==> (indices[k] as int) < i,
        decreases a.len() - i
    {
        if a[i] != 0.0 {
            let old_indices = indices.clone();
            indices.push(i);
            assert(forall|k: int| 0 <= k < indices.len() - 1 ==> indices[k] == old_indices[k]);
            assert(indices[indices.len() - 1] == i);
        }
        i = i + 1;
    }
    assert(i == a.len());
    assert(forall|k: int| 0 <= k < a.len() && a[k] != 0.0 ==> exists|j: int| 0 <= j < indices.len() && indices[j] == k);
    indices
}
// </vc-code>

}
fn main() {}