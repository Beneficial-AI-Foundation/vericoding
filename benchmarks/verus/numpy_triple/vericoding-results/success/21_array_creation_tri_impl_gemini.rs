// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): used i128 for comparison to prevent overflow */
fn create_row(i: usize, m: usize, k: i32) -> (row: Vec<f64>)
    ensures
        row.len() == m,
        forall|j: int| 0 <= j < m ==> 
            row[j] == if j <= i as int + k as int { 1.0 } else { 0.0 },
{
    let mut row: Vec<f64> = Vec::new();
    let mut j: usize = 0;
    while j < m
        invariant
            j <= m,
            row.len() == j,
            forall|col_idx: int| 0 <= col_idx < j ==> 
                row[col_idx] == if col_idx <= i as int + k as int { 1.0 } else { 0.0 },
        decreases m - j
    {
        if (j as i128) - (i as i128) <= (k as i128) {
            row.push(1.0);
        } else {
            row.push(0.0);
        }
        j = j + 1;
    }
    row
}
// </vc-helpers>

// <vc-spec>
fn tri(n: usize, m: usize, k: i32) -> (result: Vec<Vec<f64>>)
    ensures
        result.len() == n,
        forall|i: int| 0 <= i < n ==> result[i].len() == m,
        forall|i: int, j: int| 0 <= i < n && 0 <= j < m ==> 
            result[i][j] == if j <= i + k { 1.0 } else { 0.0 }
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): no changes, logic is correct */
{
    let mut result: Vec<Vec<f64>> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            i <= n,
            result.len() == i,
            forall|row_idx: int| 0 <= row_idx < i ==> result[row_idx].len() == m,
            forall|row_idx: int, col_idx: int| 0 <= row_idx < i && 0 <= col_idx < m ==> 
                result[row_idx][col_idx] == if col_idx <= row_idx as int + k as int { 1.0 } else { 0.0 },
        decreases n - i
    {
        let row = create_row(i, m, k);
        result.push(row);
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}