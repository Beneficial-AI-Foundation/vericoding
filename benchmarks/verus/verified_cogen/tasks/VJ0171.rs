// <vc-preamble>
#![crate_name = "transpose_matrix"]

use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
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
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}