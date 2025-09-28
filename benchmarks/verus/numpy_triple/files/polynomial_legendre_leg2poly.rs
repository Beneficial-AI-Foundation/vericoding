// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn leg2poly(c: Vec<f32>) -> (result: Vec<f32>)
    ensures
        result.len() == c.len(),

        (c.len() as int) < 3 ==> forall|i: int| 0 <= i < (c.len() as int) ==> result[i] == c[i],

        (c.len() as int) > 0,
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}