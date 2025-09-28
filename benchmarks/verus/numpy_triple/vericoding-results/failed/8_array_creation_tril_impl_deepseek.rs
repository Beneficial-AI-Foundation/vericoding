// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Fixed to use usize instead of int for executable code */
fn zero_matrix(rows: usize, cols: usize) -> (result: Vec<Vec<f64>>)
    ensures
        result.len() == rows,
        forall|i: int| 0 <= i < rows ==> #[trigger] result[i].len() == cols,
        forall|i: int, j: int| 0 <= i < rows && 0 <= j < cols ==> #[trigger] result[i][j] == 0.0,
{
    let mut result: Vec<Vec<f64>> = Vec::new();
    let mut i: usize = 0;
    while i < rows
        invariant
            i <= rows,
            result.len() == i,
            forall|k: int| 0 <= k < i ==> #[trigger] result[k].len() == cols,
            forall|k: int, l: int| 0 <= k < i && 0 <= l < cols ==> #[trigger] result[k][l] == 0.0,
        decreases rows - i,
    {
        let mut row: Vec<f64> = Vec::new();
        let mut j: usize = 0;
        while j < cols
            invariant
                j <= cols,
                row.len() == j,
                forall|l: int| 0 <= l < j ==> #[trigger] row[l] == 0.0,
            decreases cols - j,
        {
            row.push(0.0);
            j = j + 1;
        }
        result.push(row);
        i = i + 1;
    }
    result
}
// </vc-helpers>

// <vc-spec>
fn tril(m: Vec<Vec<f64>>, k: i32) -> (result: Vec<Vec<f64>>)
    requires 
        m.len() > 0,
        forall|i: int| 0 <= i < m.len() ==> #[trigger] m[i].len() == m[0].len(),
    ensures
        result.len() == m.len(),
        forall|i: int| 0 <= i < result.len() ==> #[trigger] result[i].len() == m[0].len(),
        forall|i: int, j: int| 
            0 <= i < result.len() && 0 <= j < result[i].len() ==> 
            #[trigger] result[i][j] == if i >= j - k { m[i][j] } else { 0.0 },
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Fixed to use usize instead of int, fixed condition expression */
{
    let nrows: usize = m.len();
    let ncols: usize = m[0].len();
    let mut result = zero_matrix(nrows, ncols);
    let mut i: usize = 0;
    while i < nrows
        invariant
            i <= nrows,
            result.len() == nrows,
            forall|k: int| 0 <= k < nrows ==> #[trigger] result[k].len() == ncols,
            forall|k: int, l: int| 
                0 <= k < i && 0 <= l < ncols ==> 
                #[trigger] result[k][l] == if k >= (l as i32) - k { m[k][l] } else { 0.0 },
            forall|k: int, l: int| 
                i <= k < nrows && 0 <= l < ncols ==> 
                #[trigger] result[k][l] == 0.0,
        decreases nrows - i,
    {
        let mut j: usize = 0;
        while j < ncols
            invariant
                j <= ncols,
                result[i].len() == ncols,
                forall|l: int| 0 <= l < j ==> 
                    #[trigger] result[i][l] == if (i as i32) >= (l as i32) - k { m[i][l] } else { 0.0 },
                forall|l: int| j <= l < ncols ==> #[trigger] result[i][l] == 0.0,
            decreases ncols - j,
        {
            if (i as i32) >= (j as i32) - k {
                result[i][j] = m[i][j];
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