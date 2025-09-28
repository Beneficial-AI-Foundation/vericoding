// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn polyval2d(x: Vec<f32>, y: Vec<f32>, c: Vec<Vec<f32>>) -> (result: Vec<f32>)
    requires 
        x@.len() == y@.len(),
        x@.len() > 0,
        c@.len() > 0,
        forall|i: int| 0 <= i < c@.len() ==> #[trigger] c@[i].len() > 0,
        forall|i: int| 0 <= i < c@.len() ==> #[trigger] c@[i].len() == c@[0].len(),
    ensures
        result@.len() == x@.len(),

        (c@.len() == 1 && c@[0].len() == 1) ==> 
            (forall|k: int| 0 <= k < result@.len() ==> #[trigger] result@[k] == c@[0][0]),

        (forall|i: int, j: int| 0 <= i < c@.len() && 0 <= j < c@[i].len() ==> #[trigger] c@[i][j] == 0.0f32) ==> 
            (forall|k: int| 0 <= k < result@.len() ==> #[trigger] result@[k] == 0.0f32),

        forall|k: int| 0 <= k < result@.len() && x@[k] == 0.0f32 && y@[k] == 0.0f32 ==> 
            #[trigger] result@[k] == c@[0][0],
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}