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
/* code modified by LLM (iteration 5): Fixed compilation error by using executable casts to i32 instead of int in the condition. */
{
    let mut result: Vec<Vec<f64>> = Vec::with_capacity(m.len());
    for i in 0..m.len() 
        invariant 
            result.len() as int == i,
            forall|k: int| 0 <= k < result.len() as int ==> #[trigger] result[k].len() == m[0].len()
    {
        let mut row: Vec<f64> = Vec::with_capacity(m[i].len());
        let m_i_len = m[i].len();
        for j in 0..m_i_len 
            invariant 
                m_i_len as int == m[i].len(),
                row.len() as int == j,
                row.len() <= m_i_len
        {
            if (i as i32) >= (j as i32) - k {
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