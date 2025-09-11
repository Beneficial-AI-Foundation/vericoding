// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn poly2leg(pol: Vec<f32>) -> (result: Vec<f32>)
    ensures 
        result.len() == pol.len(),
        forall|i: int| 0 <= i < result.len() ==> exists|c: f32| result[i] == c
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}