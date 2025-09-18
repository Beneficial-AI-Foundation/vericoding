// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Added bounds checking helper for safe arithmetic */
spec fn safe_add_le(i: usize, k: i32, j: usize) -> bool {
    i < usize::MAX && j < usize::MAX && 
    (i as int) + (k as int) <= (j as int)
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
    /* code modified by LLM (iteration 5): Fixed int casting to use only exec mode types */
    let mut result: Vec<Vec<f64>> = Vec::new();
    let rows = m.len();
    let cols = m[0].len();
    
    for i in 0..rows
        invariant
            result.len() == i,
            forall|r: int| 0 <= r < i ==> #[trigger] result[r].len() == cols,
            forall|r: int, c: int| 0 <= r < i && 0 <= c < cols && (r as i32) + k <= (c as i32) ==> #[trigger] result[r][c] == m[r][c],
            forall|r: int, c: int| 0 <= r < i && 0 <= c < cols && (r as i32) + k > (c as i32) ==> #[trigger] result[r][c] == 0.0,
    {
        let mut row: Vec<f64> = Vec::new();
        
        for j in 0..cols
            invariant
                row.len() == j,
                forall|c: int| 0 <= c < j && (i as i32) + k <= (c as i32) ==> #[trigger] row[c] == m[i][c],
                forall|c: int| 0 <= c < j && (i as i32) + k > (c as i32) ==> #[trigger] row[c] == 0.0,
        {
            if (i as i32) + k <= (j as i32) {
                row.push(m[i][j]);
            } else {
                row.push(0.0);
            }
        }
        
        result.push(row);
    }
    
    result
}
// </vc-code>

}
fn main() {}