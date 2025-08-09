#![crate_name = "transpose_matrix"]

use vstd::prelude::*;

verus! {

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
{
    let n = matrix.len();
    let mut result: Vec<Vec<i32>> = Vec::new();
    
    let mut i = 0;
    while i < n
        invariant
            0 <= i <= n,
            result.len() == i,
            forall|k: int| #![trigger result[k]]
                0 <= k < i ==> result[k].len() == n,
            forall|k: int, l: int| #![trigger result[k], matrix[l]]
                0 <= k < i && 0 <= l < n ==> result[k][l] == matrix[l][k]
    {
        let mut row: Vec<i32> = Vec::new();
        let mut j = 0;
        
        while j < n
            invariant
                0 <= j <= n,
                0 <= i < n,
                row.len() == j,
                forall|l: int| #![trigger row[l]]
                    0 <= l < j ==> row[l] == matrix[l][i]
        {
            row.push(matrix[j][i]);
            j += 1;
        }
        
        result.push(row);
        i += 1;
    }
    
    result
}

fn main() {}
}