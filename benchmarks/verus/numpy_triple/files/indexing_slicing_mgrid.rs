// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
type Matrix = Vec<Vec<f32>>;

fn mgrid(rows: usize, cols: usize, start_r: f32, stop_r: f32, start_c: f32, stop_c: f32) -> (result: (Matrix, Matrix))
    requires rows > 0 && cols > 0,
    ensures 
        result.0.len() == rows && result.1.len() == rows,
        forall|i: int| 0 <= i < rows ==> result.0[i].len() == cols && result.1[i].len() == cols,
        forall|i: int, j: int, k: int| 0 <= i < rows && 0 <= j < cols && 0 <= k < cols ==> 
            result.0[i][j] == result.0[i][k],
        forall|j: int, i: int, k: int| 0 <= j < cols && 0 <= i < rows && 0 <= k < rows ==> 
            result.1[i][j] == result.1[k][j],
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}