// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): predicate for non-zero element at index */
spec fn is_nonzero_at(a: &Vec<f64>, i: int) -> bool { 0 <= i && i < a.len() as int && a[i as usize] != 0.0 }
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
    /* code modified by LLM (iteration 5): build indices of non-zero elements with safe invariants and precomputed length */
    let mut indices: Vec<usize> = Vec::new();
    let n: int = a.len() as int;
    let mut i: int = 0;
    while i < n
        invariant 0 <= i && i <= n;
        invariant (indices.len() as int) <= i;
        invariant forall|k: int| 0 <= k && k < (indices.len() as int) ==> (indices[k as usize] as int) < n;
        decreases n - i
    {
        if a[i as usize] != 0.0 {
            indices.push(i as usize);
        }
        i = i + 1;
    }
    indices
}
// </vc-code>

}
fn main() {}