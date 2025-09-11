use vstd::prelude::*;

verus! {

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn leg2poly(c: Vec<f32>) -> (result: Vec<f32>)
    ensures
        result.len() == c.len(),

        c.len() < 3 ==> forall|i: int| 0 <= i < c.len() ==> result[i] == c[i],

        forall|i: int| 0 <= i < result.len() ==> exists|val: f32| result[i] == val,

        c.len() > 0 ==> exists|lead: f32| result[c.len() - 1] == lead,
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}