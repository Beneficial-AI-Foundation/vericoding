// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): no helpers modified */
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
/* code modified by LLM (iteration 5): fixed type mismatches by changing forall bound variables from nat to int and adding lower bounds */
    let mut result: Vec<usize> = Vec::<usize>::new();
    let mut i: usize = 0;
    while i < a.len()
        invariant
            i as int <= a.len() as int,
            forall|k: int| 0 <= k < result@.len() ==> (result@[k] as int) < (i as int) && a@[result@[k] as int] != 0.0,
            forall|l: int, m: int| 0 <= l < result@.len() && 0 <= m < result@.len() && l != m ==> result@[l] != result@[m],
            forall|l: int, m: int| 0 <= l < result@.len() && 0 <= m < result@.len() && result@[l] < result@[m] ==> l < m
    {
        if a[i] != 0.0 {
            result.push(i);
        }
        i += 1;
    }
    result
}
// </vc-code>

}
fn main() {}