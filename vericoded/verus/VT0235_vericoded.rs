// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn numpy_matrix_transpose(x: Vec<Vec<f32>>) -> (result: Vec<Vec<f32>>)
    requires 
        x@.len() > 0,
        forall|i: int| 0 <= i < x@.len() ==> x@[i].len() > 0,
        forall|i: int, j: int| 0 <= i < x@.len() && 0 <= j < x@.len() ==> x@[i].len() == x@[j].len(),
    ensures
        result@.len() == (if x@.len() > 0 { x@[0].len() } else { 0 }),
        forall|i: int| 0 <= i < result@.len() ==> result@[i].len() == x@.len(),
        forall|i: int, j: int| 0 <= i < x@.len() && 0 <= j < x@[0].len() ==> result@[j][i] == x@[i][j],
// </vc-spec>
// <vc-code>
{
    let num_rows = x.len();
    let num_cols = x[0].len();

    let mut result: Vec<Vec<f32>> = Vec::new();

    let mut j: usize = 0;
    while j < num_cols
        invariant
            num_rows == x@.len(),
            num_cols == x@[0].len(),
            forall|r: int| 0 <= r < (num_rows as int) ==> x@[r].len() == num_cols,
            0 <= j <= num_cols,
            result@.len() == j,
            forall|k: int| 0 <= k < (j as int) ==> result@[k].len() == num_rows,
            forall|k: int, l: int|
                0 <= k < (j as int) && 0 <= l < (num_rows as int) ==> result@[k][l] == x@[l][k],
        decreases num_cols - j
    {
        let mut new_row: Vec<f32> = Vec::new();
        let mut i: usize = 0;
        while i < num_rows
            invariant
                0 <= j < num_cols,
                0 <= i <= num_rows,
                num_rows == x@.len(),
                num_cols == x@[0].len(),
                forall|r: int| 0 <= r < (num_rows as int) ==> x@[r].len() == num_cols,
                new_row@.len() == i,
                forall|l: int| 0 <= l < (i as int) ==> new_row@[l] == x@[l][j as int],
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