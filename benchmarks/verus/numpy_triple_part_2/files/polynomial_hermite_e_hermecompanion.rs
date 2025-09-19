// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn hermecompanion(c: Vec<f32>) -> (mat: Vec<Vec<f32>>)
    requires 
        c@.len() >= 2,
        c[c@.len() - 1] != 0.0f32,
    ensures
        mat@.len() == c@.len() - 1,
        forall|i: int| 0 <= i < mat@.len() ==> mat@[i].len() == c@.len() - 1,
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