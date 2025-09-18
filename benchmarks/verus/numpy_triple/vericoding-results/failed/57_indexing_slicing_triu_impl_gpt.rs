// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): predicate for upper-triangular condition */
spec fn is_upper(i: int, j: int, k: int) -> bool { i + k <= j }
/* helper modified by LLM (iteration 3): executable value selector for upper triangle */
fn select_triu_value(i: usize, j: usize, k: i32, val: f64) -> f64 { if (i as i32) + k <= (j as i32) { val } else { 0.0 } }
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
/* code modified by LLM (iteration 3): fix int/usize mismatches in invariants and indexing; implement triangular fill */
{
    let rows = m.len();
    let cols = m[0].len();
    let mut res: Vec<Vec<f64>> = Vec::new();
    let mut i: usize = 0;
    while i < rows
        invariant
            i <= rows,
            res.len() == i,
            cols == m[0].len(),
            forall|r: int| 0 <= r < m.len() ==> #[trigger] m[r].len() == m[0].len(),
            forall|r: int| 0 <= r < i as int ==> #[trigger] res[r].len() == cols as int,
            forall|r: int, c: int|
                0 <= r < i as int && 0 <= c < cols as int && (r as i32) + k <= (c as i32) ==> #[trigger] res[r][c] == m[r][c],
            forall|r: int, c: int|
                0 <= r < i as int && 0 <= c < cols as int && (r as i32) + k > (c as i32) ==> #[trigger] res[r][c] == 0.0,
        decreases rows - i
    {
        let mut row: Vec<f64> = Vec::new();
        let mut j: usize = 0;
        while j < cols
            invariant
                j <= cols,
                row.len() == j,
                m[i as int].len() == cols as int,
                forall|c: int|
                    0 <= c < j as int && (i as i32) + k <= (c as i32) ==> #[trigger] row[c] == m[i as int][c],
                forall|c: int|
                    0 <= c < j as int && (i as i32) + k > (c as i32) ==> #[trigger] row[c] == 0.0,
            decreases cols - j
        {
            if (i as i32) + k <= (j as i32) {
                let val = m[i][j];
                row.push(val);
            } else {
                row.push(0.0f64);
            }
            j += 1;
        }
        res.push(row);
        i += 1;
    }
    res
}
// </vc-code>

}
fn main() {}