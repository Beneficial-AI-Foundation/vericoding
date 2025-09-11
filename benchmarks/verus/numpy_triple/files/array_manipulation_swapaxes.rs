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
        forall|i: int| 0 <= i < mat.len() ==> mat[i].len() == mat[0].len(),
        axis1 < 2,
        axis2 < 2,
    ensures
        result.len() == mat[0].len(),
        result.len() > 0 ==> result[0].len() == mat.len(),
        forall|i: int| 0 <= i < result.len() ==> result[i].len() == mat.len(),
        forall|i: int, j: int| 
            0 <= i < mat.len() && 0 <= j < mat[0].len() 
            ==> mat[i][j] == result[j][i],
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}