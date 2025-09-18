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
    /* code modified by LLM (iteration 5): fix type error by avoiding explicit int type annotations */
    let n = m.len();
    let m_cols = m[0].len();
    let mut result: Vec<Vec<f64>> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            i <= n,
            result.len() == i,
            forall|p: int| 0 <= p < i ==> #[trigger] result[p].len() == m_cols,
            forall|p: int, q: int| 0 <= p < i && 0 <= q < result[p].len() ==> #[trigger] result[p][q] == if p >= q - k { m[p][q] } else { 0.0 },
        decreases n - i
    {
        let mut row: Vec<f64> = Vec::new();
        let mut j: usize = 0;
        while j < m_cols
            invariant
                j <= m_cols,
                row.len() == j,
                i < m.len(),
                forall|q: int| 0 <= q < j ==> #[trigger] row[q] == if i as int >= q - k { m[i as int][q] } else { 0.0 },
            decreases m_cols - j
        {
            let val = if (i as int) >= (j as int) - k { m[i][j] } else { 0.0 };
            row.push(val);
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