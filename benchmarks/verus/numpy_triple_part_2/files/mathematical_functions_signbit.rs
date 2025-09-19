// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn is_negative(x: f32) -> bool;
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn signbit(x: Vec<f32>) -> (result: Vec<bool>)
    ensures 
        result.len() == x.len(),
        forall|i: int| 0 <= i < result.len() ==> result[i] == is_negative(x[i])
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