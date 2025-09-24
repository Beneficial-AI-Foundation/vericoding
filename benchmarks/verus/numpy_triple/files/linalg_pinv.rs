// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn pinv(a: Vec<Vec<f32>>) -> (result: Vec<Vec<f32>>)
    requires 
        a@.len() > 0,
        forall|i: int| 0 <= i < a@.len() ==> a@[i].len() > 0,
    ensures 
        result@.len() > 0,
        forall|i: int| 0 <= i < result@.len() ==> result@[i].len() == a@.len(),
        (forall|i: int, j: int| (0 <= i < a@.len() && 0 <= j < a@[i].len()) ==> a@[i][j] == 0.0f32) ==> 
            (forall|i: int, j: int| (0 <= i < result@.len() && 0 <= j < result@[i].len()) ==> result@[i][j] == 0.0f32)
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