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
    /* code modified by LLM (iteration 5): removed proof blocks to fix compilation error */
    let cols = m[0].len();
    let mut result: Vec<Vec<f64>> = Vec::new();
    let mut i = 0;
    while i < m.len()
        invariant
            i <= m.len(),
            result@.len() == i,
            forall|ii: int| 0 <= ii < i ==> #[trigger] result@[ii].len() == cols as int,
            forall|ii: int, jj: int| #![auto] 0 <= ii < i && 0 <= jj < cols as int && ((ii as int) + (k as int)) <= (jj as int) ==> #[trigger] result@[ii][jj] == m@[ii][jj],
            forall|ii: int, jj: int| #![auto] 0 <= ii < i && 0 <= jj < cols as int && ((ii as int) + (k as int)) > (jj as int) ==> #[trigger] result@[ii][jj] == 0.0,
        decreases m.len() - i,
    {
        let mut row: Vec<f64> = Vec::new();
        let mut j = 0;
        while j < cols
            invariant
                j <= cols,
                row@.len() == j as int,
                forall|jj: int| #![auto] 0 <= jj < j && ((i as int) + (k as int)) <= (jj as int) ==> #[trigger] row@[jj] == m@[i as int][jj],
                forall|jj: int| #![auto] 0 <= jj < j && ((i as int) + (k as int)) > (jj as int) ==> #[trigger] row@[jj] == 0.0,
            decreases cols - j,
        {
            if (i as int) + (k as int) <= (j as int) {
                row.push(m[i][j]);
            } else {
                row.push(0.0);
            }
            j += 1;
        }
        result.push(row);
        i += 1;
    }
    return result;
}
// </vc-code>

}
fn main() {}