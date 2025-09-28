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
    /* code modified by LLM (iteration 5): added opening/closing braces to fix compilation error */
    let rows: usize = m.len();
    let cols: usize = m[0].len();
    let mut result: Vec<Vec<f64>> = Vec::with_capacity(rows);
    let mut i: usize = 0;
    while i < rows
        invariant
            (i as int) >= 0,
            (i as int) <= (rows as int),
            result@.len() == (i as int),
            forall|ii: int| 0 <= ii < (i as int) ==>
                #[trigger] result@[ii].len() == (cols as int),
            forall|ii: int, jj: int|
                0 <= ii < (i as int) && 0 <= jj < (cols as int) ==>
                #[trigger] result@[ii][jj] == if ii >= jj - (k as int) { m@[ii][jj] } else { 0.0 },
        decreases (rows as int) - (i as int)
    {
        let mut row: Vec<f64> = Vec::with_capacity(cols);
        let mut j: usize = 0;
        while j < cols
            invariant
                (j as int) >= 0,
                (j as int) <= (cols as int),
                row@.len() == (j as int),
                forall|jj: int| 0 <= jj < (j as int) ==>
                    #[trigger] row@[jj] == if (i as int) >= jj - (k as int) { m@[(i as int)][jj] } else { 0.0 },
            decreases (cols as int) - (j as int)
        {
            let val = if (i as i32) >= (j as i32) - k { m[i][j] } else { 0.0 };
            row.push(val);
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