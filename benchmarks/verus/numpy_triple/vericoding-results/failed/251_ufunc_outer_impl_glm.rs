// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn outer(op: spec_fn(f64, f64) -> f64, a: Vec<f64>, b: Vec<f64>) -> (result: Vec<Vec<f64>>)
    ensures
        result.len() == a.len(),
        forall|i: int| 0 <= i < result.len() ==> result[i].len() == b.len(),
        forall|i: int, j: int| 0 <= i < a.len() && 0 <= j < b.len() ==> 
            result[i][j] == op(a[i], b[j])
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): fix compilation error by properly initializing result */
    let mut result: Vec<Vec<f64>> = Vec::new();
    let mut i = 0;
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            result.len() == i,
            forall|k: int| 0 <= k < i ==> result[k].len() == b.len(),
            forall|k: int, l: int| 0 <= k < i && 0 <= l < b.len() ==> result[k][l] == op(a[k], b[l]),
        decreases a.len() - i
    {
        let mut row: Vec<f64> = Vec::new();
        let mut j = 0;
        while j < b.len()
            invariant
                0 <= j <= b.len(),
                row.len() == j,
                forall|l: int| 0 <= l < j ==> row[l] == op(a[i], b[l]),
            decreases b.len() - j
        {
            row.push(op(a[i], b[j]));
            j += 1;
        }
        result.push(row);
        i += 1;
    }
    result
// </vc-code>


}
fn main() {}