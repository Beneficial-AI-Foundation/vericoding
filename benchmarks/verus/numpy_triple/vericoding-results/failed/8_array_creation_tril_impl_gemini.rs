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
/* code modified by LLM (iteration 5): fixed arithmetic overflow, added invariants and an assertion to prove array bounds */
{
    let mut result: Vec<Vec<f64>> = Vec::new();
    let rows = m.len();
    let cols = m[0].len();

    let mut i: usize = 0;
    while i < rows
        invariant
            m.len() > 0,
            rows == m.len(),
            cols == m[0].len(),
            forall|any_i: int| 0 <= any_i < m.len() ==> #[trigger] m[any_i].len() == cols as int,
            0 <= i <= rows,
            result.len() == i,
            forall|r: int| 0 <= r < i as int ==> #[trigger] result[r].len() == cols as int,
            forall|r: int, c: int|
                0 <= r < i as int && 0 <= c < cols as int ==> 
                #[trigger] result[r][c] == if r >= c - (k as int) { m[r][c] } else { 0.0 },
        decreases rows - i
    {
        let mut new_row = Vec::new();
        let mut j: usize = 0;

        assert(m[i].len() == cols);

        while j < cols
            invariant
                i < rows,
                m.len() > 0,
                cols == m[0].len(),
                m[i].len() == cols,
                forall|any_i: int| 0 <= any_i < m.len() ==> #[trigger] m[any_i].len() == cols as int,
                0 <= j <= cols,
                new_row.len() == j,
                forall|c: int|
                    0 <= c < j as int ==> 
                    #[trigger] new_row[c] == if i as int >= c - (k as int) { m[i as int][c] } else { 0.0 },
            decreases cols - j
        {
            let cond = i as int >= j as int - k as int;

            if cond {
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