// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn legmulx(c: Vec<f32>) -> (result: Vec<f32>)
    requires c@.len() > 0,
    ensures
        result@.len() == c@.len() + 1,
        result[0] == 0.0f32,
        result[1] == c[0],
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}