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
    /* code modified by LLM (iteration 4): Fixed type casting - use i32 for runtime comparison */
    let n = m.len();
    let m_cols = m[0].len();
    let mut result: Vec<Vec<f64>> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            0 <= i <= n,
            n == m.len(),
            m_cols == m[0].len(),
            result.len() == i,
            forall|idx: int| 0 <= idx < i ==> #[trigger] result[idx].len() == m_cols,
            forall|idx: int, jdx: int| 
                0 <= idx < i && 0 <= jdx < result[idx].len() ==> 
                #[trigger] result[idx][jdx] == if idx >= jdx - k { m[idx][jdx] } else { 0.0 },
        decreases n - i
    {
        let mut row: Vec<f64> = Vec::new();
        let mut j: usize = 0;
        while j < m_cols
            invariant
                0 <= i < n,
                0 <= j <= m_cols,
                m_cols == m[0].len(),
                row.len() == j,
                forall|idx: int| 0 <= idx < m.len() ==> #[trigger] m[idx].len() == m[0].len(),
                forall|jdx: int| 
                    0 <= jdx < j ==> 
                    #[trigger] row[jdx] == if (i as int) >= jdx - k { m[i as int][jdx] } else { 0.0 },
            decreases m_cols - j
        {
            if i as i32 >= j as i32 - k {
                row.push(m[i][j]);
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