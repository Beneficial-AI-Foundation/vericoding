// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn diagflat(v: Vec<f32>) -> (result: Vec<Vec<f32>>)
    requires v@.len() > 0,
    ensures
        result@.len() == v@.len(),
        forall|i: int| 0 <= i < result@.len() ==> result@[i].len() == v@.len(),
        forall|i: int, j: int| 0 <= i < v@.len() && 0 <= j < v@.len() && i == j ==> result@[i][j] == v@[i],
        forall|i: int, j: int| 0 <= i < v@.len() && 0 <= j < v@.len() && i != j ==> result@[i][j] == 0.0f32,
// </vc-spec>
// <vc-code>
{
    // impl-start
    assume(false);
    unreached()
    // impl-end
}
// </vc-code>


}
fn main() {}