// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn polymulx(c: Vec<f32>) -> (result: Vec<f32>)
    ensures
        result.len() == c.len() + 1,
        result[0] == 0.0f32,
        forall|i: int| 0 <= i < c@.len() ==> result[i + 1] == c[i],
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}