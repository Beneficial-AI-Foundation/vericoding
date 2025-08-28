#![crate_name = "transpose_matrix"]

use vstd::prelude::*;

verus! {

// <vc-helpers>
spec fn is_square_matrix(matrix: &Vec<Vec<i32>>) -> bool {
    matrix.len() > 0 &&
    forall|i: int| 0 <= i < matrix.len() ==> #[trigger] matrix[i].len() == matrix.len()
}

spec fn is_transpose(original: &Vec<Vec<i32>>, transposed: &Vec<Vec<i32>>) -> bool {
    transposed.len() == original[0].len() &&
    forall|i: int| 0 <= i < transposed.len() ==> #[trigger] transposed[i].len() == original.len() &&
    forall|i: int, j: int| 0 <= i < transposed.len() && 0 <= j < transposed[i].len() ==> 
        #[trigger] transposed[i][j] == original[j][i]
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
    let n = matrix.len();
    let mut result: Vec<Vec<i32>> = Vec::new();
    
    let mut i = 0;
    while i < n
        invariant
            0 <= i <= n,
            result.len() == i,
            forall|k: int| 0 <= k < i ==> result[k].len() == n,
            forall|k: int, j: int| 0 <= k < i && 0 <= j < n ==> result[k][j] == matrix[j][k]
    {
        let mut row: Vec<i32> = Vec::new();
        let mut j = 0;
        
        while j < n
            invariant
                0 <= j <= n,
                0 <= i < n,
                row.len() == j,
                forall|l: int| 0 <= l < j ==> row[l] == matrix[l as usize][i]
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

fn main() {}
}