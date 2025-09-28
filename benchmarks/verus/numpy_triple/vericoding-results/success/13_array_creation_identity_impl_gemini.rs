// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): [added explicit type annotation] */
fn create_row(i: usize, n: usize) -> (row: Vec<f64>)
    requires
        i < n,
    ensures
        row.len() == n,
        forall|l: int| 0 <= l < n ==> 
            row[l] == if i as int == l { 1.0 } else { 0.0 }
{
    let mut row: Vec<f64> = Vec::new();
    let mut j: usize = 0;
    while j < n
        invariant
            j <= n,
            row.len() == j,
            forall|l: int| 0 <= l < j ==> 
                row[l] == if i as int == l { 1.0 } else { 0.0 },
        decreases n - j
    {
        if i == j {
            row.push(1.0);
        } else {
            row.push(0.0);
        }
        j += 1;
    }
    row
}
// </vc-helpers>

// <vc-spec>
fn identity(n: usize) -> (result: Vec<Vec<f64>>)
    ensures
        result.len() == n,
        forall|i: int| 0 <= i < n ==> result[i].len() == n,
        forall|i: int, j: int| 0 <= i < n && 0 <= j < n ==>
            result[i][j] == if i == j { 1.0 } else { 0.0 }
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): [added explicit type annotation to fix compilation error] */
    let mut result: Vec<Vec<f64>> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            i <= n,
            result.len() == i,
            forall|k: int| 0 <= k < i ==> result[k].len() == n,
            forall|k: int, l: int| 0 <= k < i && 0 <= l < n ==> 
                result[k][l] == if k == l { 1.0 } else { 0.0 },
        decreases n - i
    {
        let row = create_row(i, n);
        result.push(row);
        i += 1;
    }
    result
}
// </vc-code>

}
fn main() {}