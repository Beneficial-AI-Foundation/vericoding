// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): No changes, was previously fixed */
fn create_zero_matrix(rows: usize, cols: usize) -> (result: Vec<Vec<f64>>)
    requires
        rows >= 0,
        cols >= 0,
    ensures
        result.len() == rows,
        forall|i: int| 0 <= i < result.len() ==> #[trigger] result@[i].len() == cols,
        forall|i: int, j: int| 0 <= i < result.len() && 0 <= j < result@[i].len() ==> #[trigger] result@[i][j] == 0.0,
{
    let mut result: Vec<Vec<f64>> = Vec::new();
    verus_proof_expr!{{
        assert(result.len() == 0);
        assert(forall|i: int| #![trigger result.len()] 0 <= i < result.len() ==> result@[i].len() == cols)
    }}

    while result.len() < rows
        invariant
            result.len() >= 0,
            result.len() <= rows,
            forall|i: int| 0 <= i < result.len() ==> #[trigger] result@[i].len() == cols,
            forall|i: int, j: int| 0 <= i < result.len() && 0 <= j < result@[i].len() ==> #[trigger] result@[i][j] == 0.0,
        decreases rows - result.len()
    {
        let mut row: Vec<f64> = Vec::new();
        while row.len() < cols
            invariant
                row.len() >= 0,
                row.len() <= cols,
                forall|j: int| 0 <= j < row.len() ==> #[trigger] row@[j] == 0.0,
            decreases cols - row.len()
        {
            row.push(0.0);
        }
        result.push(row);
    }
    result
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
/* code modified by LLM (iteration 5): Corrected casting within the if condition in the main loop to explicitly cast usize variables `i` and `j` to `int` when performing arithmetic comparison with `k` which is an `i8`, as `int` types are required for such operations in ghost contexts. */
{
    let rows = m.len();
    let cols = m@[0].len();
    
    let mut result = create_zero_matrix(rows, cols);

    let mut i: usize = 0;
    while i < rows
        invariant
            rows == m.len(),
            cols == m@[0].len(),
            forall|idx: int| 0 <= idx < m.len() ==> #[trigger] m@[idx].len() == m@[0].len(),
            i <= rows,
            result.len() == rows,
            forall|row_idx: int| 0 <= row_idx < result.len() ==> #[trigger] result@[row_idx].len() == cols,
            forall|row_idx: int, col_idx: int|
                0 <= row_idx < i
                && 0 <= col_idx < cols
                ==>
                    if (row_idx as int) + (k as int) <= (col_idx as int)
                    {
                        result@[row_idx][col_idx] == m@[row_idx][col_idx]
                    }
                    else
                    {
                        result@[row_idx][col_idx] == 0.0
                    },
        decreases rows - i
    {
        let mut j: usize = 0;
        while j < cols
            invariant
                rows == m.len(),
                cols == m@[0].len(),
                forall|idx: int| 0 <= idx < m.len() ==> #[trigger] m@[idx].len() == m@[0].len(),
                i < rows,
                j <= cols,
                result.len() == rows,
                result@[i].len() == cols,
                forall|row_idx: int| 0 <= row_idx < result.len() ==> #[trigger] result@[row_idx].len() == cols,
                forall|row_idx: int, col_idx: int|
                    0 <= row_idx < i
                    && 0 <= col_idx < cols
                    ==>
                        if (row_idx as int) + (k as int) <= (col_idx as int)
                        {
                            result@[row_idx][col_idx] == m@[row_idx][col_idx]
                        }
                        else
                        {
                            result@[row_idx][col_idx] == 0.0
                        },
                forall|col_idx: int|
                    0 <= col_idx < j
                    ==>
                        if (i as int) + (k as int) <= (col_idx as int)
                        {
                            result@[i][col_idx] == m@[i][col_idx]
                        }
                        else
                        {
                            result@[i][col_idx] == 0.0
                        },
            decreases cols - j
        {
            if (i as int) + (k as int) <= (j as int) { 
                result.update(i, |row: &mut Vec<f64>| { row.update(j, m@[i][j]); });
            }
            j = j + 1;
        }
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}