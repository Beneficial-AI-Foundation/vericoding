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
    /* code modified by LLM (iteration 2): fixed invariant quantifiers for k and m to resolve compilation error */
    let mut indices: Vec<usize> = Vec::new();
    let mut i: usize = 0;
    while i < a.len()
        invariant
            forall |k: int| 0 <= k < indices@.len() ==> indices@[k] as int < a@.len(),
            forall |k: int| 0 <= k < indices@.len() ==> a@[indices@[k] as int] != 0.0,
            forall |k: int| 0 <= k < indices@.len() ==> indices@[k] as int < i as int,
            forall |k: int, m: int| 0 <= k < indices@.len() && 0 <= m < indices@.len() && k < m ==> (indices@[k] as int < indices@[m] as int),
            forall |k: int, m: int| 0 <= k < indices@.len() && 0 <= m < indices@.len() && k != m ==> indices@[k] != indices@[m],
            forall |j: int| 0 <= j < (i as int) && a@[j] != 0.0 ==> exists |k: int| 0 <= k < indices@.len() && indices@[k] as int == j,
        decreases a@.len() - (i as int)
    {
        if a[i] != 0.0 {
            indices.push(i);
        }
        i += 1;
    }
}
// </vc-code>

}
fn main() {}