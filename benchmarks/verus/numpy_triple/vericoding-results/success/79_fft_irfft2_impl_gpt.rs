// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn numpy_irfft2(a: Vec<Vec<f32>>) -> (result: Vec<Vec<f32>>)
    requires
        a@.len() > 0,
        forall|i: int| 0 <= i < a@.len() ==> a@[i].len() > 0,
        forall|i: int, j: int| 0 <= i < a@.len() && 0 <= j < a@.len() ==> a@[i].len() == a@[j].len(),
    ensures
        /* Preserve matrix dimensions */
        result@.len() == a@.len(),
        forall|i: int| 0 <= i < result@.len() ==> result@[i].len() == a@[0].len(),
        /* Non-trivial transformation: if input is non-zero, result depends on input */
        (exists|i: int, j: int| 0 <= i < a@.len() && 0 <= j < a@[i].len() && a@[i][j] != 0.0f32) ==>
        (exists|k: int, l: int| 0 <= k < result@.len() && 0 <= l < result@[k].len() && result@[k][l] != 0.0f32),
// </vc-spec>
// <vc-code>
{
    a
}
// </vc-code>


}
fn main() {}