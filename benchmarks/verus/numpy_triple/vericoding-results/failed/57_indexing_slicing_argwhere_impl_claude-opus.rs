// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn argwhere(a: &Vec<f64>) -> (indices: Vec<usize>)
    ensures
        forall|i: int| 0 <= i < indices@.len() ==> (#[trigger] indices@[i] as int) < a@.len(),
        forall|i: int| 0 <= i < indices@.len() ==> a@[indices@[i] as int] != 0.0,
        forall|i: int| 0 <= i < a@.len() && a@[i] != 0.0 ==> exists|j: int| 0 <= j < indices@.len() && indices@[j] as int == i,
        forall|i: int, j: int| 0 <= i < indices@.len() && 0 <= j < indices@.len() && i != j ==> indices@[i] != indices@[j],
        forall|i: int, j: int| 0 <= i < indices@.len() && 0 <= j < indices@.len() && (indices@[i] as int) < (indices@[j] as int) ==> i < j,
        (indices@.len() == 0) == (forall|i: int| 0 <= i < a@.len() ==> a@[i] == 0.0),
// </vc-spec>
// <vc-code>
{
    let mut indices = Vec::new();
    let mut i = 0;
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            forall|j: int| 0 <= j < indices@.len() ==> (#[trigger] indices@[j] as int) < a@.len(),
            forall|j: int| 0 <= j < indices@.len() ==> a@[indices@[j] as int] != 0.0,
            forall|j: int| 0 <= j < i && a@[j] != 0.0 ==> exists|k: int| 0 <= k < indices@.len() && indices@[k] as int == j,
            forall|j: int| i <= j < a@.len() && a@[j] != 0.0 ==> forall|k: int| 0 <= k < indices@.len() ==> indices@[k] as int != j,
            forall|j: int, k: int| 0 <= j < indices@.len() && 0 <= k < indices@.len() && j != k ==> indices@[j] != indices@[k],
            forall|j: int, k: int| 0 <= j < indices@.len() && 0 <= k < indices@.len() && (indices@[j] as int) < (indices@[k] as int) ==> j < k,
            forall|j: int| 0 <= j < indices@.len() ==> (indices@[j] as int) < i,
        decreases a.len() - i
    {
        if a[i] != 0.0 {
            indices.push(i);
        }
        i = i + 1;
    }
    indices
}
// </vc-code>

}
fn main() {}