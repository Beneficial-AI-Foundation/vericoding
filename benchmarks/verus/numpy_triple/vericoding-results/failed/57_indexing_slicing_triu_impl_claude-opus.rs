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
{
    /* code modified by LLM (iteration 5): fixed type casting for exec code */
    let n = m.len();
    let m_cols = m[0].len();
    let mut result: Vec<Vec<f64>> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            i <= n,
            result.len() == i,
            forall|ii: int| 0 <= ii < i ==> #[trigger] result[ii].len() == m_cols,
            forall|ii: int, jj: int| 0 <= ii < i && 0 <= jj < result[ii].len() && (ii as i32) + k <= (jj as i32) ==> #[trigger] result[ii][jj] == m[ii][jj],
            forall|ii: int, jj: int| 0 <= ii < i && 0 <= jj < result[ii].len() && (ii as i32) + k > (jj as i32) ==> #[trigger] result[ii][jj] == 0.0,
        decreases n - i
    {
        let mut row: Vec<f64> = Vec::new();
        let mut j: usize = 0;
        while j < m_cols
            invariant
                i < n,
                j <= m_cols,
                row.len() == j,
                m[i as int].len() == m_cols,
                forall|jj: int| 0 <= jj < j && (i as i32) + k <= (jj as i32) ==> #[trigger] row[jj] == m[i as int][jj],
                forall|jj: int| 0 <= jj < j && (i as i32) + k > (jj as i32) ==> #[trigger] row[jj] == 0.0,
            decreases m_cols - j
        {
            if i as i32 <= i32::MAX - k.abs() && j as i32 <= i32::MAX && (i as i32) + k <= (j as i32) {
                let val = m[i][j];
                row.push(val);
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