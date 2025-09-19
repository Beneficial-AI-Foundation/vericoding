// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
spec fn is_square_matrix(matrix: Seq<Seq<i32>>) -> bool {
    matrix.len() > 0 && forall|i: int| 0 <= i < matrix.len() ==> matrix[i].len() == matrix.len()
}

spec fn primary_diagonal_sum(matrix: Seq<Seq<i32>>, idx: nat) -> int
    decreases matrix.len() - idx
{
    if idx >= matrix.len() || !is_square_matrix(matrix) {
        0
    } else {
        (matrix[idx as int][idx as int] as int) + primary_diagonal_sum(matrix, idx + 1)
    }
}

spec fn secondary_diagonal_sum(matrix: Seq<Seq<i32>>, idx: nat) -> int
    decreases matrix.len() - idx
{
    if idx >= matrix.len() || !is_square_matrix(matrix) {
        0
    } else {
        (matrix[idx as int][(matrix.len() - 1 - idx) as int] as int) + secondary_diagonal_sum(matrix, idx + 1)
    }
}

fn diagonal_difference(matrix: Vec<Vec<i32>>) -> (result: i32)
    requires 
        matrix.len() > 0,
        forall|i: int| 0 <= i < matrix.len() ==> matrix[i]@.len() == matrix.len(),
    ensures 
        matrix.len() == 1 ==> result == 0,
        result >= 0,
// </vc-spec>
// <vc-code>
{
    // impl-start
    assume(false);
    0
    // impl-end
}
// </vc-code>


}
fn main() {
    // let test_matrix = vec![vec![11, 2, 4], vec![4, 5, 6], vec![10, 8, -12]];
    // println!("{}", diagonal_difference(test_matrix));
    
    // let test_matrix2 = vec![vec![1, 2], vec![3, 4]];
    // println!("{}", diagonal_difference(test_matrix2));
    
    // let test_matrix3 = vec![vec![5]];
    // println!("{}", diagonal_difference(test_matrix3));
}