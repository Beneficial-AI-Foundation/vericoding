// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): fixed should_keep function to handle integer conversion properly */
spec fn should_keep(i: int, j: int, k: i32) -> bool {
    (i as i32) + k <= (j as i32)
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
/* code modified by LLM (iteration 5): fixed iterator issues and added proper bounds checking */
{
    let mut result: Vec<Vec<f64>> = Vec::new();
    let n = m.len();
    let col_len = m[0].len();
    for i in 0..n
        invariant 
            0 <= i <= n,
            result@.len() == i,
            forall|idx: int| 0 <= idx < i ==> #[trigger] result@[idx]@.len() == col_len,
            forall|idx: int, j: int| 
                0 <= idx < i && 0 <= j < col_len && should_keep(idx, j, k) ==> #[trigger] result@[idx]@[j] == m@[idx]@[j],
            forall|idx: int, j: int| 
                0 <= idx < i && 0 <= j < col_len && !should_keep(idx, j, k) ==> #[trigger] result@[idx]@[j] == 0.0,
    {
        let mut new_row: Vec<f64> = Vec::new();
        for j in 0..col_len
            invariant 
                j <= col_len,
                new_row@.len() == j as int,
                forall|col: int| 0 <= col < (j as int) ==> (
                    should_keep(i as int, col, k) ==> new_row@[col] == m@[i as int]@[col]
                ),
                forall|col: int| 0 <= col < (j as int) ==> (
                    !should_keep(i as int, col, k) ==> new_row@[col] == 0.0
                ),
        {
            if should_keep(i as int, j as int, k) {
                new_row.push(m[i][j]);
            } else {
                new_row.push(0.0);
            }
        }
        result.push(new_row);
    }
    result
}
// </vc-code>

}
fn main() {}