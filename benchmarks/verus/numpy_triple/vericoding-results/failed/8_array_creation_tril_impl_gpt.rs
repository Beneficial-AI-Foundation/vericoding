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
    let rows = m.len();
    let cols = m[0].len();
    let mut result: Vec<Vec<f64>> = Vec::new();
    let mut i: usize = 0;
    while i < rows
        invariant
            result.len() == i,
            i <= rows,
            rows == m.len(),
            cols == m[0].len(),
            forall|r: int| 0 <= r < result.len() ==> #[trigger] result[r].len() == cols,
            forall|r: int, c: int|
                0 <= r < result.len() && 0 <= c < result[r].len() ==>
                #[trigger] result[r][c] == if r >= c - (k as int) { m[r][c] } else { 0.0 },
        decreases (rows as int) - (i as int)
    {
        let mut rowv: Vec<f64> = Vec::new();
        assert(m[i].len() == cols);
        let mut j: usize = 0;
        while j < cols
            invariant
                rowv.len() == j,
                j <= cols,
                cols == m[0].len(),
                i < rows,
                m[i].len() == cols,
                forall|c: int|
                    0 <= c < rowv.len() ==>
                    #[trigger] rowv[c] == if (i as int) >= c - (k as int) { m[i][c] } else { 0.0 },
            decreases (cols as int) - (j as int)
        {
            assert(i < m.len());
            assert(m[i].len() == cols);
            assert(j < m[i].len());
            let cond: bool = (i as int) >= (j as int) - (k as int);
            let val = if cond { m[i][j] } else { 0.0 };
            rowv.push(val);
            j = j + 1;
        }
        result.push(rowv);
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}