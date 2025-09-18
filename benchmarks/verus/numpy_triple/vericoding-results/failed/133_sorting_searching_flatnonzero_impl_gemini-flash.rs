// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn flatnonzero(a: Vec<f64>) -> (result: Vec<usize>)
    ensures

        forall|i: int| 0 <= i < result.len() ==> a[result[i] as int] != 0.0,

        forall|j: int| 0 <= j < a.len() && a[j] != 0.0 ==> exists|k: int| 0 <= k < result.len() && result[k] == j,

        forall|i: int, j: int| 0 <= i < result.len() && 0 <= j < result.len() && i != j ==> result[i] != result[j],

        forall|i: int, j: int| 0 <= i < j < result.len() ==> result[i] < result[j],
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Cast usize to int for array indexing in invariant. */
{
    let mut result: Vec<usize> = Vec::new();
    let mut i: usize = 0;
    while i < a.len()
        invariant (
            0 <= i && i <= a.len(),
            forall|k: int| 0 <= k < result.len() ==> a[result[k] as int] != 0.0,
            forall|k: int| 0 <= k < result.len() ==> result[k] <= i,
            forall|k: int, l: int| 0 <= k < result.len() && 0 <= l < result.len() && k != l ==> result[k] != result[l],
            forall|k: int, l: int| 0 <= k < l < result.len() ==> result[k] < result[l],
            forall|j: int| 0 <= j && j < i ==> (a[j] != 0.0 ==> exists|k: int| 0 <= k < result.len() && result[k] == j),
        )
    {
        if a[i] != 0.0 {
            result.push(i);
        }
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}