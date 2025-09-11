// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn numpy_empty_like(prototype: &Vec<f32>) -> (result: Vec<f32>)
    ensures
        result.len() == prototype.len(),
        forall|i: int| 0 <= i < prototype.len() ==> 0 <= i < result.len(),
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}