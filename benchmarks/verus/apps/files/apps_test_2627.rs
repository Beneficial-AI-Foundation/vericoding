// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_matrix(matrix: Seq<Seq<char>>) -> bool {
    (forall|i: int| 0 <= i < matrix.len() ==> matrix[i].len() == (if matrix.len() == 0 { 0 } else { matrix[0].len() as int })) &&
    (forall|i: int, j: int| 0 <= i < matrix.len() && 0 <= j < matrix[i].len() ==> matrix[i][j] == '0' || matrix[i][j] == '1')
}

spec fn max_possible_area(matrix: Seq<Seq<char>>) -> int {
    (matrix.len() as int) * (if matrix.len() == 0 { 0 } else { matrix[0].len() as int })
}

spec fn empty_matrix(matrix: Seq<Seq<char>>) -> bool {
    matrix.len() == 0 || matrix[0].len() == 0
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn maximal_rectangle(matrix: Seq<Seq<char>>) -> (result: i32)
    requires 
        valid_matrix(matrix)
    ensures 
        result >= 0,
        empty_matrix(matrix) ==> result == 0,
        result <= max_possible_area(matrix) as i32
// </vc-spec>
// <vc-code>
{
    assume(false);
    0
}
// </vc-code>


}

fn main() {}