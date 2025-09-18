// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): kept is_non_zero helper */
spec fn is_non_zero(x: f64) -> bool { x != 0.0 }
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
/* code modified by LLM (iteration 5): fixed trigger syntax in loop invariants */
{
    let mut indices: Vec<usize> = Vec::new();
    let mut i = 0;
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            forall|k: int| 0 <= k < indices.len() ==> (#[trigger indices[k]] indices[k] < a.len()),
            forall|k: int| 0 <= k < indices.len() ==> (#[trigger indices[k]] a[indices[k] as int] != 0.0),
            forall|k: int| 0 <= k < i && a[k] != 0.0 ==> (#[trigger k] exists|j: int| 0 <= j < indices.len() && indices[j] == k),
            forall|k: int, l: int| 0 <= k < indices.len() && 0 <= l < indices.len() && k != l ==> indices[k] != indices[l],
            forall|k: int, l: int| 0 <= k < indices.len() && 0 <= l < indices.len() && (indices[k] as int) < (indices[l] as int) ==> k < l,
        decreases a.len() - i
    {
        if a[i] != 0.0 {
            indices.push(i);
            assert(a[indices[indices.len()-1] as int] != 0.0);
            assert(exists|j: int| 0 <= j < indices.len() && indices[j] == i);
        }
        i = i + 1;
    }
    indices
}
// </vc-code>

}
fn main() {}