// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

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
/* code modified by LLM (iteration 5): Fixed indexing types for `m` within the nested loop to use `usize` for array access consistent with `Vec<usize>` indexing, and `int` for other calculations. */{
    let rows = m.len();
    let cols = m[0].len();
    let mut result: Vec<Vec<f64>> = vec![];

    let mut i = 0;
    while i < rows
        invariant
            result.len() == i,
            forall|row_idx: int| 0 <= row_idx < i ==> #[trigger] result[row_idx].len() == cols,
            forall|row_idx: int, col_idx: int|
                0 <= row_idx < i && 0 <= col_idx < cols && (row_idx as i32) + k <= (col_idx as i32)
                ==>
                result[row_idx][col_idx] == m[row_idx as usize][col_idx as usize],
            forall|row_idx: int, col_idx: int|
                0 <= row_idx < i && 0 <= col_idx < cols && (row_idx as i32) + k > (col_idx as i32)
                ==>
                result[row_idx][col_idx] == 0.0,
    {
        let mut row: Vec<f64> = vec![];
        
        let mut j = 0;
        while j < cols
            invariant
                row.len() == j,
                forall|col_idx: int| 0 <= col_idx < j && (i as i32) + k <= (col_idx as i32)
                    ==>
                    row[col_idx] == m[i as usize][col_idx as usize],
                forall|col_idx: int| 0 <= col_idx < j && (i as i32) + k > (col_idx as i32)
                    ==>
                    row[col_idx] == 0.0,
        {
            if (i as i32) + k <= (j as i32) {
                row.push(m[i as usize][j as usize]);
            } else {
                row.push(0.0);
            }
            j = j + 1;
        }
        result.push(row);
        i = i + 1;
    }

    result
}
// </vc-code>

}
fn main() {}