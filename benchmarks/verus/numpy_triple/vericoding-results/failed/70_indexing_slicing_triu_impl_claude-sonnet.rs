// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

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
    /* code modified by LLM (iteration 5): moved int casts to ghost context using proof blocks */
    let mut result: Vec<Vec<f64>> = Vec::new();
    let n = m.len();
    let m_cols = m[0].len();
    
    let mut i = 0;
    while i < n
        invariant
            i <= n,
            result.len() == i,
            forall|idx: int| 0 <= idx < i ==> #[trigger] result@[idx].len() == m_cols,
            forall|row: int, col: int| 0 <= row < i && 0 <= col < m_cols && row + (k as int) <= col ==> #[trigger] result@[row][col] == m@[row][col],
            forall|row: int, col: int| 0 <= row < i && 0 <= col < m_cols && row + (k as int) > col ==> #[trigger] result@[row][col] == 0.0,
    {
        let mut row: Vec<f64> = Vec::new();
        let mut j = 0;
        
        while j < m_cols
            invariant
                j <= m_cols,
                row.len() == j,
                forall|col: int| 0 <= col < j && (i as int) + (k as int) <= col ==> #[trigger] row@[col] == m@[(i as int)][col],
                forall|col: int| 0 <= col < j && (i as int) + (k as int) > col ==> #[trigger] row@[col] == 0.0,
        {
            let should_fill = {
                proof {
                    let i_int = i as int;
                    let j_int = j as int;
                    let k_int = k as int;
                    i_int + k_int <= j_int
                }
            };
            
            if should_fill {
                row.push(m[i][j]);
            } else {
                row.push(0.0);
            }
            j += 1;
        }
        
        result.push(row);
        i += 1;
    }
    
    result
}
// </vc-code>

}
fn main() {}