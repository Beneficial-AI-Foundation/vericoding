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
        forall|i: int| 0 <= i < mat.len() ==> mat[i].len() == mat[0].len(),
    ensures

        result.len() == mat[0].len(),
        forall|i: int| 0 <= i < result.len() ==> result[i].len() == mat.len(),

        forall|i: int, j: int| 0 <= i < result.len() && 0 <= j < result[i].len() ==> 
            result[i][j] == mat[j][i],
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}