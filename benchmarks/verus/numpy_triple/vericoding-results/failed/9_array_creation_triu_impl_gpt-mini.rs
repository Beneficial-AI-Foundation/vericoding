// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): compute keeps predicate using int arithmetic */
fn keeps(i: usize, j: usize, k: i8) -> bool
    ensures
        result == ((i as int) <= (j as int) - (k as int)),
{
    let ii: int = i as int;
    let jj: int = j as int;
    let kk: int = k as int;
    ii <= jj - kk
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
    /* code modified by LLM (iteration 5): build result by copying upper triangle and zeroing others */
    let n = m.len();
    let mut result: Vec<Vec<f32>> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            result.len() == i,
            forall|ii: int| 0 <= ii && ii < result@.len() ==> result@[ii].len() == m@[ii].len(),
        decreases n - i
    {
        let row = &m[i];
        let row_len = row.len();
        let mut new_row: Vec<f32> = Vec::new();
        let mut j: usize = 0;
        while j < row_len
            invariant
                new_row.len() == j,
                forall|jj: int| 0 <= jj && jj < new_row@.len() ==> #[trigger] new_row@[jj] == if (i as int) > (jj as int) - (k as int) { 0.0f32 } else { m@[i as int][jj as int] },
            decreases row_len - j
        {
            if keeps(i, j, k) {
                new_row.push(row[j]);
            } else {
                new_row.push(0.0f32);
            }
            j += 1;
        }
        result.push(new_row);
        i += 1;
    }
    result
}

// </vc-code>


}
fn main() {}