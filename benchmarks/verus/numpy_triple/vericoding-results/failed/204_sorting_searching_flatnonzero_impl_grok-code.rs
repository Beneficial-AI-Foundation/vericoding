// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): no helpers modified */
// </vc-helpers>

// <vc-spec>
fn flatnonzero(a: Vec<f64>) -> (result: Vec<usize>)
    ensures

        forall|i: int| 0 <= i < result@.len() ==> a[result@[i] as int] != 0.0,

        forall|j: int| 0 <= j < a@.len() && a@[j] != 0.0 ==> exists|k: int| 0 <= k < result@.len() && result@[k] == j,

        forall|i: int, j: int| 0 <= i < result@.len() && 0 <= j < result@.len() && i != j ==> result@[i] != result@[j],

        forall|i: int, j: int| 0 <= i < j < result@.len() ==> result@[i] < result@[j],
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): changed invariant from < to <= to maintain after pushing current index */
{
    let mut result: Vec<usize> = Vec::new();
    let mut i: usize = 0;
    while i < a.len()
        invariant
            0 <= i as int <= a@.len(),
            forall|k: int| 0 <= k < result@.len() ==> (result@[k] <= i as int && a@[result@[k] as int] != 0.0),
            forall|j: usize| 0 <= j as int < i as int ==> (a@[j as int] != 0.0 ==> result@.contains(j as usize)),
            forall|m: int, n: int| 0 <= m < n < result@.len() ==> result@[m] < result@[n],
            result@.no_duplicates(),
        decreases a@.len() - i as int
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