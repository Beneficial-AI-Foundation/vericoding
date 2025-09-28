// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn triu(m: &Vec<Vec<f32>>, k: i8) -> (result: Vec<Vec<f32>>)
    requires 
        m@.len() > 0,
        forall|i: int| 0 <= i < m@.len() ==> #[trigger] m@[i].len() == m@[0].len(),
    ensures
        result@.len() == m@.len(),
        forall|i: int| 0 <= i < result@.len() ==> #[trigger] result@[i].len() == m@[i].len(),
        forall|i: int, j: int| 
            0 <= i < result@.len() && 0 <= j < result@[i].len() ==>
            #[trigger] result@[i][j] == if i > j - k as int { 0.0f32 } else { m@[i][j] },
        forall|i: int, j: int|
            0 <= i < result@.len() && 0 <= j < result@[i].len() && i <= j - k as int ==>
            #[trigger] result@[i][j] == m@[i][j],
        forall|i: int, j: int|
            0 <= i < result@.len() && 0 <= j < result@[i].len() && i > j - k as int ==>
            #[trigger] result@[i][j] == 0.0f32,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Fixed compilation error by replacing 'as int' with 'as i64' in executable code to avoid using ghost types illegally */
    let rows = m.len();
    let cols = m[0].len();
    let mut result: Vec<Vec<f32>> = Vec::with_capacity(rows);
    let mut i: usize = 0;
    while i < rows
        invariant
            result@.len() == i as int,
            m@.len() == rows as int,
            forall|ii: int| 0 <= ii < i as int ==> ii < m@.len(),
            forall|ii: int, jj: int| 0 <= ii < i as int && 0 <= jj < cols as int ==> jj < m@[ii].len() && #[trigger] result@[ii][jj] == if ii > jj - k as int { 0.0f32 } else { m@[ii][jj] },
        decreases rows - i
    {
        let mut row: Vec<f32> = Vec::with_capacity(cols);
        let mut j: usize = 0;
        while j < cols
            invariant
                row@.len() == j as int,
                forall|jj: int| 0 <= jj < j as int ==> jj < m@[i as nat].len() && #[trigger] row@[jj] == if i as int > jj - k as int { 0.0f32 } else { m@[i as nat][jj] },
            decreases cols - j
        {
            if (i as i64) > (j as i64) - (k as i64) {
                row.push(0.0f32);
            } else {
                row.push(m[i][j]);
            }
            j += 1;
        }
        result.push(row);
        i += 1;
    }
    result
}
// </vc-code>


}
fn main() {}