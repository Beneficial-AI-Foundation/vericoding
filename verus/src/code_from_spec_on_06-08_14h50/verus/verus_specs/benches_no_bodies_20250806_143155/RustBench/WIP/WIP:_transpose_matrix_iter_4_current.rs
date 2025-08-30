#![crate_name = "transpose_matrix_impl"]
use vstd::prelude::*;

verus! {

#[verifier::loop_isolation(false)]
fn transpose(matrix: Vec<Vec<i32>>) -> (result: Vec<Vec<i32>>)
    requires
        matrix.len() > 0,
        forall|i: int| #![trigger matrix[i]]
            0 <= i < matrix.len() ==> matrix[i].len() == matrix[0].len(),
    ensures
        result.len() == matrix[0].len(),
        forall|i: int| #![trigger result[i]]
            0 <= i < result.len() ==> result[i].len() == matrix.len(),
        forall|i: int, j: int| #![trigger result[i], matrix[j]]
            0 <= i < result.len() && 0 <= j < result[i].len() ==> result[i][j] == matrix[j][i]
{
    let mut result: Vec<Vec<i32>> = Vec::new();
    let rows = matrix.len();
    let cols = matrix[0].len();
    
    // Initialize result matrix with correct dimensions
    let mut i = 0;
    /* code modified by LLM (iteration 1): added decreases clause and fixed invariants for verification */
    while i < cols
        invariant
            result.len() == i,
            forall|k: int| 0 <= k < i ==> result[k].len() == rows,
            forall|k: int, l: int| 0 <= k < i && 0 <= l < rows ==> result[k][l] == matrix[l][k],
            i <= cols,
            cols == matrix[0].len(),
            rows == matrix.len(),
            rows > 0,
            forall|m: int| 0 <= m < matrix.len() ==> matrix[m].len() == cols
        decreases cols - i
    {
        let mut new_row: Vec<i32> = Vec::new();
        let mut j = 0;
        /* code modified by LLM (iteration 2): fixed type casting issue in invariant */
        while j < rows
            invariant
                new_row.len() == j,
                result.len() == i,
                forall|k: int| 0 <= k < i ==> result[k].len() == rows,
                forall|k: int, l: int| 0 <= k < i && 0 <= l < rows ==> result[k][l] == matrix[l][k],
                forall|l: int| 0 <= l < j ==> new_row[l] == matrix[l][i as int],
                j <= rows,
                i < cols,
                cols == matrix[0].len(),
                rows == matrix.len(),
                forall|m: int| 0 <= m < matrix.len() ==> matrix[m].len() == cols
            decreases rows - j
        {
            new_row.push(matrix[j][i]);
            j += 1;
        }
        result.push(new_row);
        i += 1;
    }
    
    result
}

fn main() {}
}