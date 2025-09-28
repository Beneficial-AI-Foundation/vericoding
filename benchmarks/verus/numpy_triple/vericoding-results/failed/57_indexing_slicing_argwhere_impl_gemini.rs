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
    /* code modified by LLM (iteration 5): added triggers to invariants to guide verification */
    let mut indices: Vec<usize> = Vec::new();
    let mut i: usize = 0;
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            forall|k: int| 0 <= k < indices@.len() ==> (#[trigger] indices@[k] as int) < i,
            forall|k: int| 0 <= k < indices@.len() ==> a@[(#[trigger] indices@[k]) as int] != 0.0,
            forall|j: int| 0 <= j < i && #[trigger] a@[j] != 0.0 ==> 
                exists|k: int| 0 <= k < indices@.len() && indices@[k] as int == j,
            forall|k1: int, k2: int| 0 <= k1 < k2 < indices@.len() ==> 
                (#[trigger] indices@[k1]) < (#[trigger] indices@[k2]),
        decreases a.len() - i
    {
        if a[i] != 0.0 {
            assert(forall|k: int| 0 <= k < indices@.len() ==> (#[trigger] indices@[k] as int) < i);
            indices.push(i);
        }
        i = i + 1;
    }
    indices
}
// </vc-code>

}
fn main() {}