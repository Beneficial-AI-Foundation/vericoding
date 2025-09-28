// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): No helper modifications needed. */

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
/* code modified by LLM (iteration 5): Corrected type issue with `a[j as usize]` inside quantifier and ensure that `result` is properly initialized. */
{
    let mut result = Vec::new();
    let mut i: usize = 0;
    while i < a.len()
        invariant transform_array_to_seq(
            0 <= i as int,
            i as int <= a.len() as int,
            forall|j: int| 0 <= j < result.len() ==> a[result[j] as int] != 0.0,
            forall|j: int| 0 <= j < i as int && a[j as usize] != 0.0 ==> exists|k: int| 0 <= k < result.len() && result[k] == j as usize,
            forall|x: int, y: int| 0 <= x < result.len() && 0 <= y < result.len() && x != y ==> result[x] != result[y],
            forall|x: int, y: int| 0 <= x < y < result.len() ==> result[x] < result[y],
        ),
        decreases a.len() - i,
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