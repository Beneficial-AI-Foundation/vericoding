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

        c.len() < 3 ==> forall|i: int| #![trigger result[i]] 0 <= i < c.len() ==> result[i] == c[i],

        true, // Polynomial coefficients exist (simplified)

        true, // Leading coefficient exists (simplified)
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}