// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): fixed type conversions in ghost indexing and quantifier bounds */
fn triu_row(m: &Vec<Vec<f64>>, k: i8, i: usize) -> (row: Vec<f64>)
    requires
        i < m@.len(),
    ensures
        row@.len() == m@[0].len(),
        forall|j: int| 0 <= j < row@.len() ==> 
            if (i as int) + (k as int) <= j {
                row@[j] == m@[i as int]@[j]
            } else {
                row@[j] == 0.0
            }
{
    let mut row = Vec::new();
    let n = m[0].len();
    for j in 0..n
        invariant
            row@.len() == j,
            forall|col: int| 0 <= col < (j as int) ==> 
                if (i as int) + (k as int) <= col {
                    row@[col] == m@[i as int]@[col]
                } else {
                    row@[col] == 0.0
                }
    {
        if (i as int) + (k as int) <= (j as int) {
            row.push(m[i][j]);
        } else {
            row.push(0.0);
        }
    }
    row
}
// </vc-helpers>

// <vc-spec>
fn triu(m: Vec<Vec<f64>>, k: i8) -> (result: Vec<Vec<f64>>)
    requires 
        m.len() > 0,
        forall|i: int| 0 <= i < m@.len() ==> #[trigger] m@[i].len() == m@[0].len(),
    ensures
        result.len() == m.len(),
        forall|i: int| 0 <= i < result@.len() ==> #[trigger] result@[i].len() == m@[0].len(),
        forall|i: int, j: int| 0 <= i < result@.len() && 0 <= j < result@[i].len() && i + (k as int) <= j ==> #[trigger] result@[i][j] == m@[i][j],
        forall|i: int, j: int| 0 <= i < result@.len() && 0 <= j < result@[i].len() && i + (k as int) > j ==> #[trigger] result@[i][j] == 0.0,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fixed type conversions in loop invariant quantifier bounds */
    let mut result: Vec<Vec<f64>> = Vec::new();
    let n_rows = m.len();
    for i in 0..n_rows
        invariant
            result@.len() == i,
            forall|row_idx: int| 0 <= row_idx < (i as int) ==> 
                result@[row_idx]@.len() == m@[0].len(),
            forall|row_idx: int, col_idx: int| 
                0 <= row_idx < (i as int) && 0 <= col_idx < m@[0].len() ==> 
                    if (row_idx as int) + (k as int) <= col_idx {
                        result@[row_idx][col_idx] == m@[row_idx]@[col_idx]
                    } else {
                        result@[row_idx][col_idx] == 0.0
                    }
    {
        let row = triu_row(&m, k, i);
        result.push(row);
    }
    result
}
// </vc-code>

}
fn main() {}