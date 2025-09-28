// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn hermval2d(x: Vec<f32>, y: Vec<f32>, c: Vec<Vec<f32>>) -> (result: Vec<f32>)
    requires 
        x.len() == y.len(),
    ensures 
        result.len() == x.len(),

        c.len() == 0 ==> forall|k: int| 0 <= k < result.len() ==> result[k] == 0.0f32,
        c.len() > 0 && c@[0].len() == 0 ==> forall|k: int| 0 <= k < result.len() ==> result[k] == 0.0f32,
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}