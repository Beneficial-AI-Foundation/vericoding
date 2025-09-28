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
    /* code modified by LLM (iteration 5): added decreases clause to fix verification error */
    let mut result: Vec<Vec<f32>> = Vec::new();
    let mut i: usize = 0;
    while i < m.len()
        invariant
            0 <= i <= m@.len(),
            result@.len() == i,
            forall|row_idx: int| 0 <= row_idx < i ==> #[trigger] result@[row_idx].len() == m@[row_idx].len(),
            forall|row_idx: int, col_idx: int| 
                0 <= row_idx < i && 0 <= col_idx < result@[row_idx].len() ==>
                #[trigger] result@[row_idx][col_idx] == if row_idx > col_idx - k as int { 0.0f32 } else { m@[row_idx][col_idx] },
        decreases m@.len() - i
    {
        let mut row: Vec<f32> = Vec::new();
        let mut j: usize = 0;
        while j < m[i].len()
            invariant
                0 <= i < m@.len(),
                0 <= j as int <= m@[i as int].len() as int,
                row@.len() == j,
                forall|col_idx: int|
                    0 <= col_idx < j as int ==>
                    #[trigger] row@[col_idx] == if i as int > col_idx - k as int { 0.0f32 } else { m@[i as int][col_idx] },
            decreases m@[i as int].len() - j as int
        {
            if i as i8 > j as i8 - k {
                row.push(0.0f32);
            } else {
                row.push(m[i][j]);
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