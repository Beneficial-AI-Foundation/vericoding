// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): None needed */
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
/* code modified by LLM (iteration 5): Use integer types for loop counters */
{
    let rows = m.len();
    let cols = m[0].len();
    let mut result = Vec::new();

    let mut i: usize = 0;
    while i < rows
        invariant
            0 <= i as int <= rows as int,
            result.len() == i,
            forall|idx: int| 0 <= idx < i as int ==> #[trigger] result[idx].len() == cols,
            forall|idx: int, jdx: int|
                0 <= idx < i as int && 0 <= jdx < cols as int ==> 
                #[trigger] result[idx][jdx] == if idx >= jdx - k { m[idx][jdx] } else { 0.0 },
    {
        let mut current_row = Vec::new();
        let mut j: usize = 0;
        while j < cols
            invariant
                0 <= j as int <= cols as int,
                current_row.len() == j,
                forall|jdx: int| 0 <= jdx < j as int ==> 
                    current_row[jdx] == if i as int >= jdx - k { 
                        m[i][jdx]
                    } else {
                        0.0
                    },
        {
            if i as int >= j as int - k {
                current_row.push(m[i][j]);
            } else {
                current_row.push(0.0);
            }
            j = j + 1;
        }
        result.push(current_row);
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}