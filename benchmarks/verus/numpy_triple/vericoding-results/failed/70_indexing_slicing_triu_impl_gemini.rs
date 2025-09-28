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
    /* code modified by LLM (iteration 5): added assert for index bounds and an explicit trigger */
    let mut result: Vec<Vec<f64>> = Vec::new();
    let rows = m.len();
    let cols = m[0].len();

    let mut i: usize = 0;
    while i < rows
        invariant
            0 <= i <= rows,
            result.len() == i,
            m.len() == rows,
            m[0].len() == cols,
            forall|l: int| 0 <= l < m@.len() ==> #[trigger] m@[l].len() == m@[0].len(),
            forall|row_idx: int| 0 <= row_idx < (i as int) ==> #[trigger] result@[row_idx].len() == cols,
            forall|row_idx: int, col_idx: int|
                0 <= row_idx < (i as int) && 0 <= col_idx < cols ==>
                (if row_idx + (k as int) <= col_idx {
                    result@[row_idx][col_idx] == m@[row_idx][col_idx]
                } else {
                    result@[row_idx][col_idx] == 0.0
                }),
        decreases rows - i
    {
        let mut new_row: Vec<f64> = Vec::new();
        let mut j: usize = 0;

        assert(m[i].len() == cols);

        while j < cols
            invariant
                i < rows,
                m.len() == rows,
                m[0].len() == cols,
                m[i].len() == cols,
                forall|l: int| 0 <= l < m@.len() ==> #[trigger] m@[l].len() == m@[0].len(),
                0 <= j <= cols,
                new_row.len() == j,
                forall|col_idx: int|
                    0 <= col_idx < (j as int) ==>
                    (if (i as int) + (k as int) <= col_idx {
                        new_row@[col_idx] == m@[i as int][col_idx]
                    } else {
                        new_row@[col_idx] == 0.0
                    }),
            decreases cols - j
        {
            if (i as int) + (k as int) <= (j as int) {
                new_row.push(m[i][j]);
            } else {
                new_row.push(0.0);
            }
            j = j + 1;
        }
        result.push(new_row);
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}