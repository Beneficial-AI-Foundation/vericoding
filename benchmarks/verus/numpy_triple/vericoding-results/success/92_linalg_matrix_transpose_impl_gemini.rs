// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn numpy_matrix_transpose(x: Vec<Vec<f32>>) -> (result: Vec<Vec<f32>>)
    requires 
        x.len() > 0,
        forall|i: int| 0 <= i < x.len() ==> x[i].len() > 0,
        forall|i: int, j: int| 0 <= i < x.len() && 0 <= j < x.len() ==> x[i].len() == x[j].len(),
    ensures
        result.len() == (if x.len() > 0 { x[0].len() } else { 0 }),
        forall|i: int| 0 <= i < result.len() ==> result[i].len() == x.len(),
        forall|i: int, j: int| 0 <= i < x.len() && 0 <= j < x[0].len() ==> result[j][i] == x[i][j],
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): added decreases clauses to loops */
    let num_rows = x.len();
    let num_cols = x[0].len();

    assert forall|i: int| 0 <= i < x.len() implies x[i].len() == num_cols by {
        assert(x[i].len() == x[0].len());
    }

    let mut result: Vec<Vec<f32>> = Vec::new();
    let mut j: usize = 0;
    while j < num_cols
        invariant
            0 <= j <= num_cols,
            num_rows == x.len(),
            num_cols == x[0].len(),
            forall|i: int| 0 <= i < x.len() ==> x[i].len() == num_cols,
            result.len() == j,
            forall|k: int| 0 <= k < j ==> result[k].len() == num_rows,
            forall|c: int, r: int| 0 <= c < j && 0 <= r < num_rows ==> result[c][r] == x[r][c],
        decreases num_cols - j
    {
        let mut new_row: Vec<f32> = Vec::new();
        let mut i: usize = 0;
        while i < num_rows
            invariant
                0 <= i <= num_rows,
                0 <= j < num_cols,
                num_rows == x.len(),
                forall|k: int| 0 <= k < x.len() ==> x[k].len() == num_cols,
                new_row.len() == i,
                forall|k: int| 0 <= k < i ==> new_row[k] == x[k][j as int],
            decreases num_rows - i
        {
            new_row.push(x[i][j]);
            i = i + 1;
        }
        result.push(new_row);
        j = j + 1;
    }
    result
}
// </vc-code>

}
fn main() {}