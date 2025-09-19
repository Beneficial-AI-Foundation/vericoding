// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn lagder(c: Vec<f32>, m: u8, scl: f32) -> (result: Vec<f32>)
    requires c.len() > 0,
    ensures
        result.len() == c.len(),
        m as nat == 0 ==> (forall|i: int| 0 <= i < c@.len() ==> result@[i] == c@[i]),
        (m as nat >= c@.len() && c@.len() > 0) ==> (forall|i: int| 0 <= i < result@.len() ==> result@[i] == 0.0f32),
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