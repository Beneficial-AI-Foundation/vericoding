// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn lagval3d(x: Vec<f32>, y: Vec<f32>, z: Vec<f32>, c: Vec<Vec<Vec<f32>>>) -> (result: Vec<f32>)
    requires 
        x.len() == y.len(),
        y.len() == z.len(),
        x.len() > 0,
        c.len() > 0,
        c[0].len() > 0,
        c[0][0].len() > 0,
    ensures
        result.len() == x.len(),
        result.len() == y.len(), 
        result.len() == z.len(),

        (c.len() == 1 && c[0].len() == 1 && c[0][0].len() == 1) ==> 
            forall|i: int| 0 <= i < result.len() ==> result[i] == c[0][0][0],
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}