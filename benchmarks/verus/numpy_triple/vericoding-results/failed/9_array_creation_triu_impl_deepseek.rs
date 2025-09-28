// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

/* helper modified by LLM (iteration 5): remove ghost type conversions and use proper usize arithmetic */
fn get_row(r: usize, m: &Vec<Vec<f32>>) -> (row: Vec<f32>)
    requires
        0 <= r < m@.len(),
    ensures
        row@ == m@[r],
{
    m[r].clone()
}

fn set_at_row_col(row: usize, col: usize, value: f32, m: &mut Vec<Vec<f32>>)
    requires
        old(m)@.len() > 0,
        0 <= row < old(m)@.len(),
        0 <= col < old(m)@[row].len(),
        forall|i: int| 0 <= i < old(m)@.len() ==> #[trigger] old(m)@[i].len() == old(m)@[0].len(),
    ensures
        m@.len() == old(m)@.len(),
        forall|i: int| 0 <= i < m@.len() ==> #[trigger] m@[i].len() == old(m)@[0].len(),
        m@ == old(m)@.set(row as int, old(m)@[row].set(col as int, value)),
{
    m[row][col] = value;
}

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
    /* code modified by LLM (iteration 5): use usize arithmetic to avoid ghost type conversion errors */
    let mut result = m.clone();
    let rows = m.len();
    
    let mut i: usize = 0;
    while i < rows
        invariant
            0 <= i <= rows,
            result@.len() == m@.len(),
            forall|r: int| 0 <= r < result@.len() ==> #[trigger] result@[r].len() == m@[0].len(),
            forall|r: int, c: int| 
                0 <= r < result@.len() && 0 <= c < result@[r].len() && r < i ==> 
                #[trigger] result@[r][c] == if (r as int) > (c as int) - (k as int) { 0.0f32 } else { m@[r][c] },
    {
        let row = get_row(i, &result);
        let mut j: usize = 0;
        while j < row.len()
            invariant
                0 <= j <= row.len(),
                result@.len() == m@.len(),
                forall|r: int| 0 <= r < result@.len() ==> #[trigger] result@[r].len() == m@[0].len(),
                forall|r: int, c: int| 
                    0 <= c < j && r == i ==> 
                    #[trigger] result@[r][c] == if (r as int) > (c as int) - (k as int) { 0.0f32 } else { m@[r][c] },
                forall|r: int, c: int| 
                    r != i || c >= j ==> 
                    #[trigger] result@[r][c] == m@[r][c],
        {
            if (i as int) > (j as int) - (k as int) {
                set_at_row_col(i, j, 0.0f32, &mut result);
            }
            j = j + 1;
        }
        i = i + 1;
    }
    result
}
// </vc-code>


}
fn main() {}