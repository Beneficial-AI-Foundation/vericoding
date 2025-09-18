// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Aligned spec with `triu` using `i32` casts and fixed compilation error using `i64` in the conditional. */
fn create_row(row: &Vec<f64>, row_idx: usize, k: i32) -> (result: Vec<f64>)
    ensures
        result.len() == row.len(),
        forall|j: int| 0 <= j < result.len() && (row_idx as i32) + k <= (j as i32) ==> result[j] == row[j],
        forall|j: int| 0 <= j < result.len() && (row_idx as i32) + k > (j as i32) ==> result[j] == 0.0,
{
    let mut new_row: Vec<f64> = Vec::new();
    let mut j: usize = 0;
    while j < row.len()
        invariant
            j <= row.len(),
            new_row.len() == j,
            forall|idx: int| 0 <= idx < j && (row_idx as i32) + k <= (idx as i32) ==> new_row[idx] == row[idx],
            forall|idx: int| 0 <= idx < j && (row_idx as i32) + k > (idx as i32) ==> new_row[idx] == 0.0,
        decreases row.len() - j,
    {
        if (row_idx as i64) + (k as i64) > (j as i64) {
            new_row.push(0.0);
        } else {
            new_row.push(row[j]);
        }
        j = j + 1;
    }
    new_row
}
// </vc-helpers>

// <vc-spec>
fn triu(m: Vec<Vec<f64>>, k: i32) -> (result: Vec<Vec<f64>>)
    requires 
        m.len() > 0,
        forall|i: int| 0 <= i < m.len() ==> #[trigger] m[i].len() == m[0].len(),
    ensures
        result.len() == m.len(),
        forall|i: int| 0 <= i < result.len() ==> #[trigger] result[i].len() == m[0].len(),
        forall|i: int, j: int| 0 <= i < result.len() && 0 <= j < result[i].len() && (i as i32) + k <= (j as i32) ==> #[trigger] result[i][j] == m[i][j],
        forall|i: int, j: int| 0 <= i < result.len() && 0 <= j < result[i].len() && (i as i32) + k > (j as i32) ==> #[trigger] result[i][j] == 0.0,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Aligned loop invariants with the triu spec by using i32 casts. */
    let mut result_matrix: Vec<Vec<f64>> = Vec::new();
    let mut i: usize = 0;
    while i < m.len()
        invariant
            m.len() > 0,
            forall|idx: int| 0 <= idx < m.len() ==> #[trigger] m[idx].len() == m[0].len(),
            i <= m.len(),
            result_matrix.len() == i,
            forall|row_idx: int| 0 <= row_idx < i ==> #[trigger] result_matrix[row_idx].len() == m[0].len(),
            forall|row_idx: int, col_idx: int|
                0 <= row_idx < i && 0 <= col_idx < m[0].len() && (row_idx as i32) + k <= (col_idx as i32)
                ==> #[trigger] result_matrix[row_idx][col_idx] == m[row_idx][col_idx],
            forall|row_idx: int, col_idx: int|
                0 <= row_idx < i && 0 <= col_idx < m[0].len() && (row_idx as i32) + k > (col_idx as i32)
                ==> #[trigger] result_matrix[row_idx][col_idx] == 0.0,
        decreases m.len() - i,
    {
        let new_row = create_row(&m[i], i, k);
        result_matrix.push(new_row);
        i = i + 1;
    }
    result_matrix
}
// </vc-code>

}
fn main() {}