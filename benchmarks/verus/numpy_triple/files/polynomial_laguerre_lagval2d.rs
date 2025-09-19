// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn lagval2d(x: Vec<f32>, y: Vec<f32>, c: Vec<Vec<f32>>) -> (result: Vec<f32>)
    requires 
        x@.len() == y@.len(),
        x@.len() > 0,
        c@.len() > 0,
        forall|i: int| 0 <= i < c@.len() ==> c@[i].len() > 0,
    ensures
        result@.len() == x@.len(),

        (c@.len() == 1 && c@[0].len() == 1) ==> 
            forall|i: int| 0 <= i < result@.len() ==> result@[i] == c@[0][0],

        result@.len() == x@.len() && result@.len() == y@.len(),
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}