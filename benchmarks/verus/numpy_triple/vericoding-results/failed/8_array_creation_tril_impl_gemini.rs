// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

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
{
    /* code modified by LLM (iteration 5): fixed invariants and used safe arithmetic for condition */
    let mut result: Vec<Vec<f64>> = Vec::new();
    let rows = m.len();
    let cols = m[0].len();
    let mut i: usize = 0;

    while i < rows
        invariant
            0 <= i <= rows,
            rows == m.len(),
            cols == m[0].len(),
            forall|row_idx: int| 0 <= row_idx < rows ==> #[trigger] m[row_idx].len() == cols,
            result.len() == i,
            forall|row_idx: int| 0 <= row_idx < i ==> #[trigger] result[row_idx].len() == cols,
            forall|r: int, c: int|
                0 <= r < i && 0 <= c < cols ==> 
                #[trigger] result[r][c] == if r >= c - (k as int) { m[r][c] } else { 0.0 },
        decreases rows - i
    {
        let mut new_row: Vec<f64> = Vec::new();
        let mut j: usize = 0;
        
        while j < cols
            invariant
                0 <= j <= cols,
                i < rows,
                new_row.len() == j,
                forall|c: int| 0 <= c < j ==> 
                    #[trigger] new_row[c] == if (i as int) >= c - (k as int) { m[i as int][c] } else { 0.0 },
            decreases cols - j
        {
            // The condition is i >= j - k. This is equivalent to i - j >= -k.
            // This form avoids overflow. Vec length is <= isize::MAX, so i and j fit into i64.
            // The difference (i - j) will also fit in i64.
            if (i as i64) - (j as i64) >= -(k as i64) {
                new_row.push(m[i][j]);
            } else {
                new_row.push(0.0);
            }
            j += 1;
        }
        
        result.push(new_row);
        i += 1;
    }
    
    result
}

// </vc-code>

}
fn main() {}