// <vc-preamble>
#![crate_name = "transpose_matrix"]

use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): fixed type consistency for matrix indexing */
spec fn is_square_matrix(matrix: &Vec<Vec<i32>>) -> bool {
    matrix.len() > 0 &&
    forall|i: int| #![trigger matrix[i]] 0 <= i < matrix.len() ==> matrix[i].len() == matrix[0].len() &&
    forall|i: int| #![trigger matrix[i]] 0 <= i < matrix.len() ==> matrix[i].len() == matrix.len()
}

spec fn valid_transpose(matrix: &Vec<Vec<i32>>, result: &Vec<Vec<i32>>) -> bool {
    result.len() == matrix[0].len() &&
    forall|i: int| #![trigger result[i]] 0 <= i < result.len() ==> result[i].len() == matrix.len() &&
    forall|i: int, j: int| #![trigger result[i], matrix[j]] 0 <= i < result.len() && 0 <= j < result[i].len() ==> result[i][j] == matrix[j][i]
}
// </vc-helpers>

// <vc-spec>
#[verifier::loop_isolation(false)]
fn transpose(matrix: Vec<Vec<i32>>) -> (result: Vec<Vec<i32>>)
    requires
        matrix.len() > 0,
        forall|i: int| #![trigger matrix[i]]
            0 <= i < matrix.len() ==> matrix[i].len() == matrix[0].len(),
        forall|i: int| #![trigger matrix[i]]
            0 <= i < matrix.len() ==> matrix[i].len() == matrix.len()
    ensures
        result.len() == matrix[0].len(),
        forall|i: int| #![trigger result[i]]
            0 <= i < result.len() ==> result[i].len() == matrix.len(),
        forall|i: int, j: int| #![trigger result[i], matrix[j]]
            0 <= i < result.len() && 0 <= j < result[i].len() ==> result[i][j] == matrix[j][i]
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 4): added decreases clause to loops */
    let n = matrix.len();
    let m = matrix[0].len();
    
    let mut result: Vec<Vec<i32>> = Vec::new();
    
    let mut i = 0;
    while i < m
        invariant
            0 <= i <= m,
            result.len() == i,
            forall|k: int| #![trigger result[k]] 0 <= k < i ==> result[k].len() == n,
            forall|k: int, l: int| #![trigger result[k], matrix[l]] 0 <= k < i && 0 <= l < n ==> result[k][l] == matrix[l][k]
        decreases m - i
    {
        let mut row: Vec<i32> = Vec::new();
        
        let mut j = 0;
        while j < n
            invariant
                0 <= j <= n,
                0 <= i < m,
                row.len() == j,
                forall|l: int| #![trigger row[l]] 0 <= l < j ==> row[l] == matrix[l][i as int]
            decreases n - j
        {
            row.push(matrix[j][i]);
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