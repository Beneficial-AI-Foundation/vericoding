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
    /* code modified by LLM (iteration 5): fixed type errors in loop invariants */
    let mut result: Vec<Vec<f64>> = Vec::new();
    let mut i: usize = 0;
    while i < m.len()
        invariant
            0 <= i <= m.len(),
            result.len() == i,
            forall|ii: int| 0 <= ii < i ==> #[trigger] result@[ii].len() == m@[0].len(),
            forall|ii: int, j: int| 0 <= ii < i && 0 <= j < result@[ii].len() && ii + (k as int) <= j ==> #[trigger] result@[ii][j] == m@[ii][j],
            forall|ii: int, j: int| 0 <= ii < i && 0 <= j < result@[ii].len() && ii + (k as int) > j ==> #[trigger] result@[ii][j] == 0.0,
    {
        let mut row: Vec<f64> = Vec::new();
        let mut j: usize = 0;
        while j < m[i].len()
            invariant
                0 <= i < m.len(),
                0 <= j <= m@[i].len(),
                row.len() == j,
                forall|jj: int| 0 <= jj < j && (i as int) + (k as int) <= jj ==> #[trigger] row@[jj] == m@[i][jj],
                forall|jj: int| 0 <= jj < j && (i as int) + (k as int) > jj ==> #[trigger] row@[jj] == 0.0,
        {
            if (i as i64) + (k as i64) <= (j as i64) {
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