// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn numpy_full_like(a: Vec<f32>, fill_value: f32) -> (result: Vec<f32>)
    ensures 
        result.len() == a.len(),
        forall|i: int| 0 <= i < result.len() ==> result[i] == fill_value,
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}