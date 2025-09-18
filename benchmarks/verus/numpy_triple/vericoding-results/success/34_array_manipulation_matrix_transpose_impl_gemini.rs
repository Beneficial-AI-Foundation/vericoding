// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn matrix_transpose(mat: &Vec<Vec<f32>>) -> (result: Vec<Vec<f32>>)
    requires 
        mat.len() > 0,
        forall|i: int| #![trigger mat[i]] 0 <= i < mat.len() ==> mat[i].len() == mat[0].len(),
    ensures

        result.len() == mat[0].len(),
        forall|i: int| #![trigger result[i]] 0 <= i < result.len() ==> result[i].len() == mat.len(),

        forall|i: int, j: int| #![trigger result[i][j]] 0 <= i < result.len() && 0 <= j < result[i].len() ==> 
            result[i][j] == mat[j][i],
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): add matrix dimension invariants to inner loop */
    let rows = mat.len();
    let cols = mat[0].len();

    let mut result: Vec<Vec<f32>> = Vec::with_capacity(cols);

    let mut i: usize = 0;
    while i < cols
        invariant
            mat.len() > 0,
            forall|k: int| #![trigger mat[k]] 0 <= k < mat.len() ==> mat[k].len() == mat[0].len(),
            rows == mat.len(),
            cols == mat[0].len(),
            0 <= i <= cols,
            result.len() == i,
            forall|k: int| #![trigger result[k]] 0 <= k < i ==> result[k].len() == rows,
            forall|k: int, l: int| #![trigger result[k][l]] 0 <= k < i && 0 <= l < rows ==> result[k][l] == mat[l][k],
        decreases cols - i,
    {
        let mut new_row: Vec<f32> = Vec::with_capacity(rows);
        let mut j: usize = 0;
        while j < rows
            invariant
                i < cols,
                rows == mat.len(),
                cols == mat[0].len(),
                forall|k: int| #![trigger mat[k]] 0 <= k < mat.len() ==> mat[k].len() == mat[0].len(),
                0 <= j <= rows,
                new_row.len() == j,
                forall|l: int| #![trigger new_row[l]] 0 <= l < j ==> new_row[l] == mat[l][i as int],
            decreases rows - j,
        {
            new_row.push(mat[j][i]);
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