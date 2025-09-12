// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn valid_matrix(matrix: Seq<Seq<String>>) -> bool {
    (forall|i: int| 0 <= i < matrix.len() ==> matrix[i].len() == (if matrix.len() == 0 { 0 } else { matrix[0].len() })) &&
    (forall|i: int, j: int| 0 <= i < matrix.len() && 0 <= j < matrix[i].len() ==> matrix[i][j]@ == "0".to_string_lossy() || matrix[i][j]@ == "1".to_string_lossy())
}

spec fn max_possible_area(matrix: Seq<Seq<String>>) -> int {
    (matrix.len() as int) * (if matrix.len() == 0 { 0 } else { matrix[0].len() as int })
}

spec fn empty_matrix(matrix: Seq<Seq<String>>) -> bool {
    matrix.len() == 0 || matrix[0].len() == 0
}
// </vc-helpers>

// <vc-spec>
fn maximal_rectangle(matrix: Seq<Seq<String>>) -> (result: int)
    requires 
        valid_matrix(matrix),
    ensures 
        result >= 0,
        empty_matrix(matrix) ==> result == 0,
        result <= max_possible_area(matrix),
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>


}

fn main() {}