// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
spec fn vec_sum(a: Seq<f32>) -> f32;

fn sum(a: Vec<f32>) -> (result: f32)
    ensures 
        result == vec_sum(a@),
        a.len() == 0 ==> result == 0.0f32,
        (forall|i: int| 0 <= i < a.len() ==> a[i] == 0.0f32) ==> result == 0.0f32,
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}