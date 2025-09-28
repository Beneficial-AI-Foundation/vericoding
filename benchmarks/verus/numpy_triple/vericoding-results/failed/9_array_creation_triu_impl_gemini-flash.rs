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
    /* code modified by LLM (iteration 5): Fixed compilation error by removing `as int` casts for `i` and `j` in the comparison `i > j - k as int`, as these variables are already `nat` and treated as integers in expressions. This ensures that the comparison is done between concrete integer types, which is acceptable in an `exec` context. The `k as int` is kept because `k` is `i8` and needs to be promoted to a larger integer type for arithmetic operation with `j`. */
    let n_rows = m@.len();
    let n_cols = m@[0].len();
    let mut result: Vec<Vec<f32>> = Vec::new();

    let mut i: nat = 0;
    while i < n_rows
        invariant
            0 <= i as int <= n_rows as int,
            result@.len() == i,
            forall|idx: int| 0 <= idx < i ==> result@[idx].len() == n_cols,
            forall|idx: int, jdx: int|
                0 <= idx < i && 0 <= jdx < n_cols ==> {
                    #[trigger] result@[idx][jdx] == if idx > jdx - k as int { 0.0f32 } else { m@[idx][jdx] }
                },
        decreases n_rows - i
    {
        let mut current_row: Vec<f32> = Vec::new();
        let mut j: nat = 0;
        while j < n_cols
            invariant
                0 <= j as int <= n_cols as int,
                current_row@.len() == j,
                forall|jdx: int| 0 <= jdx < j ==> {
                    #[trigger] current_row@[jdx] == if i > jdx - k as int { 0.0f32 } else { m@[i][jdx] }
                },
            decreases n_cols - j
        {
            if i > j - k as int {
                current_row.push(0.0f32);
            } else {
                current_row.push(m@[i][j]);
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