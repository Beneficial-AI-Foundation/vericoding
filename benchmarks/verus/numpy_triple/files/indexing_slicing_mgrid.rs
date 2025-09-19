// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
type Matrix = Vec<Vec<f32>>;

fn mgrid(rows: u8, cols: u8, start_r: f32, stop_r: f32, start_c: f32, stop_c: f32) -> (result: (Matrix, Matrix))
    requires rows > 0 && cols > 0,
    ensures 
        result.0.len() == rows as nat && result.1.len() == rows as nat,
        forall|i: int| 0 <= i < rows as int ==> result.0[i].len() == cols as nat && result.1[i].len() == cols as nat,
        forall|i: int, j: int, k: int| 0 <= i < rows as int && 0 <= j < cols as int && 0 <= k < cols as int ==> 
            result.0[i][j] == result.0[i][k],
        forall|j: int, i: int, k: int| 0 <= j < cols as int && 0 <= i < rows as int && 0 <= k < rows as int ==> 
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