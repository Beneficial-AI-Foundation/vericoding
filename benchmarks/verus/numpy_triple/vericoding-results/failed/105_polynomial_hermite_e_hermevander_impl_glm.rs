// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): removed outer block to fix compilation error */
fn compute_hermite_row(x: f64, deg: usize) -> (row: Vec<f64>)
    ensures
        row.len() == deg + 1,
        row[0] == 1.0,
        deg > 0 ==> row[1] == x,
{
    let mut row = Vec::with_capacity(deg+1);
    row.push(1.0);
    if deg >= 1 {
        row.push(x);
        let mut d = 2;
        while d <= deg
            invariant
                2 <= d <= deg + 1,
                row.len() == d
        {
            let prev1 = row[d-1];
            let prev2 = row[d-2];
            let next_val = x * prev1 - (d-1) as f64 * prev2;
            row.push(next_val);
            d += 1;
        }
    }
    row
}
// </vc-helpers>

// <vc-spec>
fn hermevander(x: Vec<f64>, deg: usize) -> (result: Vec<Vec<f64>>)
    requires deg >= 0,
    ensures
        result.len() == x.len(),
        forall|i: int| 0 <= i < result.len() ==> result[i].len() == deg + 1,
        forall|i: int| 0 <= i < result.len() ==> result[i][0] == 1.0,
        deg > 0 ==> forall|i: int| 0 <= i < result.len() ==> result[i][1] == x[i],
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): no changes needed, helper function compilation fixed */
    let mut result: Vec<Vec<f64>> = Vec::with_capacity(x.len());
    let mut i = 0;
    while i < x.len()
        invariant
            0 <= i <= x.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i ==> #[trigger] result[j].len() == deg + 1,
            forall|j: int| 0 <= j < i ==> result[j][0] == 1.0,
            deg > 0 ==> forall|j: int| 0 <= j < i ==> #[trigger] result[j][1] == x[j],
    {
        let row = compute_hermite_row(x[i], deg);
        result.push(row);
        i += 1;
    }
    result
}
// </vc-code>

}
fn main() {}