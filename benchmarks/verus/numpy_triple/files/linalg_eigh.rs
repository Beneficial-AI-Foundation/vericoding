// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
struct EighResult {
    eigenvalues: Vec<f32>,
    eigenvectors: Vec<Vec<f32>>,
}

fn eigh(a: Vec<Vec<f32>>) -> (result: EighResult)
    requires 
        a.len() > 0,
        forall|i: int| 0 <= i < a.len() ==> a[i]@.len() == a.len(),
        forall|i: int, j: int| 0 <= i < a.len() && 0 <= j < a.len() ==> a[i][j] == a[j][i],
    ensures
        result.eigenvalues.len() == a.len(),
        result.eigenvectors.len() == a.len(),
        forall|i: int| 0 <= i < result.eigenvectors.len() ==> result.eigenvectors[i]@.len() == a.len(),
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}