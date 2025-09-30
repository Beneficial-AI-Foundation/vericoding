// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn poly2herme(pol: Vec<f32>) -> (result: Vec<f32>)
    ensures
        result.len() == pol.len(),
        forall|i: int| 0 <= i < pol@.len() && pol[i as int] != 0.0f32 ==> exists|j: int| 0 <= j < result@.len() && result[j as int] != 0.0f32,
        (exists|i: int| 0 <= i < pol@.len() && pol[i as int] != 0.0f32) ==> (exists|j: int| 0 <= j < result@.len() && result[j as int] != 0.0f32),
// </vc-spec>
// <vc-code>
{
    pol
}
// </vc-code>


}
fn main() {}