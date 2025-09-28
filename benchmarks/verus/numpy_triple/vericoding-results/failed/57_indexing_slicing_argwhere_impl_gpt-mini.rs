// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): removed inner proof block to avoid spec proof-block error */
proof fn trivial_helper()
    ensures
        true,
{
}

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
    /* code modified by LLM (iteration 2): implement argwhere loop collecting nonzero indices */
    let mut indices: Vec<usize> = Vec::new();
    let mut i: usize = 0;
    while i < a.len()
        invariant
            0 <= (i as int) && (i as int) <= a@.len(),
            forall|k: int| 0 <= k < indices@.len() ==> (indices@[k] as int) < (i as int),
            forall|k: int| 0 <= k < indices@.len() ==> a@[indices@[k] as int] != 0.0,
            forall|j: int| 0 <= j < (i as int) && a@[j] != 0.0 ==> exists|k: int| 0 <= k < indices@.len() && (indices@[k] as int) == j,
            forall|k: int, l: int| 0 <= k < indices@.len() && 0 <= l < indices@.len() && k != l ==> indices@[k] != indices@[l],
            forall|k: int, l: int| 0 <= k < indices@.len() && 0 <= l < indices@.len() && (indices@[k] as int) < (indices@[l] as int) ==> k < l,
        decreases
            a.len() - i
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