// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Removed requires/ensures from spec functions */
spec fn int_to_usize_spec(x: int) -> usize
{
    x as usize
}

spec fn usize_to_int_spec(x: usize) -> int
{
    x as int
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
{
    /* code modified by LLM (iteration 5): Simplified implementation with correct tril logic */
    let mut result: Vec<Vec<f64>> = Vec::new();
    
    for i in 0..m.len()
        invariant
            result.len() == i,
            forall|row_idx: int| 0 <= row_idx < result.len() ==> #[trigger] result[row_idx].len() == m[0].len(),
            forall|row_idx: int, col_idx: int| 
                0 <= row_idx < result.len() && 0 <= col_idx < result[row_idx].len() ==> 
                #[trigger] result[row_idx][col_idx] == if row_idx >= col_idx - k { m[row_idx][col_idx] } else { 0.0 },
    {
        let mut row: Vec<f64> = Vec::new();
        
        for j in 0..m[i].len()
            invariant
                i < m.len(),
                row.len() == j,
                result.len() == i,
                forall|row_idx: int| 0 <= row_idx < result.len() ==> #[trigger] result[row_idx].len() == m[0].len(),
                forall|row_idx: int, col_idx: int| 
                    0 <= row_idx < result.len() && 0 <= col_idx < result[row_idx].len() ==> 
                    #[trigger] result[row_idx][col_idx] == if row_idx >= col_idx - k { m[row_idx][col_idx] } else { 0.0 },
                forall|col_idx: int| 
                    0 <= col_idx < row.len() ==> 
                    #[trigger] row[col_idx] == if i as int >= col_idx - k { m[i as int][col_idx] } else { 0.0 },
        {
            let value = if (i as int) >= (j as int) - (k as int) {
                m[i][j]
            } else {
                0.0
            };
            row.push(value);
        }
        
        result.push(row);
    }
    
    result
}
// </vc-code>

}
fn main() {}