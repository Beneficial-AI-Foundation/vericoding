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
{
    /* code modified by LLM (iteration 5): Fixed int usage - using usize for array indexing */
    let mut result: Vec<Vec<f64>> = Vec::new();
    let mut i: usize = 0;
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            result.len() == i,
            forall|k: int| 0 <= k < i ==> result[k as int].len() == b.len(),
            forall|k: int, j: int| 0 <= k < i && 0 <= j < b.len() ==> result[k as int][j as int] == op(a[k as int], b[j as int]),
        decreases a.len() - i
    {
        let mut row: Vec<f64> = Vec::new();
        let mut j: usize = 0;
        while j < b.len()
            invariant
                0 <= j <= b.len(),
                row.len() == j,
                forall|k: int| 0 <= k < j ==> row[k as int] == op(a[i as int], b[k as int]),
            decreases b.len() - j
        {
            let val: f64 = choose|v: f64| v == op(a[i], b[j]);
            row.push(val);
            j += 1;
        }
        result.push(row);
        i += 1;
    }
    result
}
// </vc-code>


}
fn main() {}