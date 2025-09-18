// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn swapaxes(mat: Vec<Vec<f32>>, axis1: usize, axis2: usize) -> (result: Vec<Vec<f32>>)
    requires
        mat.len() > 0,
        mat[0].len() > 0,
        forall|i: int| #![trigger mat[i]] 0 <= i < mat.len() ==> mat[i].len() == mat[0].len(),
        axis1 < 2,
        axis2 < 2,
    ensures
        result.len() == mat[0].len(),
        result.len() > 0 ==> result[0].len() == mat.len(),
        forall|i: int| #![trigger result[i]] 0 <= i < result.len() ==> result[i].len() == mat.len(),
        forall|i: int, j: int| #![trigger result[j][i]]
            0 <= i < mat.len() && 0 <= j < mat[0].len() 
            ==> mat[i][j] == result[j][i],
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 3): added decreases clauses to loops */
{
    let rows = mat.len();
    let cols = mat[0].len();
    let mut result: Vec<Vec<f32>> = Vec::new();

    let mut j: usize = 0;
    while j < cols
        invariant
            rows == mat.len(),
            cols == mat[0].len(),
            forall|r: int| 0 <= r < mat.len() ==> mat[r].len() == cols,
            j <= cols,
            result.len() == j,
            forall|k: int| 0 <= k < j ==> result@[k].len() == rows,
            forall|k: int, i: int| #![trigger result@[k]@[i]]
                0 <= k < j && 0 <= i < rows ==> result@[k]@[i] == mat@[i]@[k],
        decreases cols - j
    {
        let mut new_row: Vec<f32> = Vec::new();
        let mut i: usize = 0;
        while i < rows
            invariant
                rows == mat.len(),
                cols == mat[0].len(),
                forall|r: int| 0 <= r < mat.len() ==> mat[r].len() == cols,
                j < cols,
                i <= rows,
                new_row.len() == i,
                forall|k: int| 0 <= k < i ==> new_row@[k] == mat@[k]@[j as int],
            decreases rows - i
        {
            new_row.push(mat[i][j]);
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