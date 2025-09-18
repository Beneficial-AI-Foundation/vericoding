// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
fn always_false() -> bool { false }
// </vc-helpers>

// <vc-spec>
fn may_share_memory(a: &Vec<f32>, b: &Vec<f32>) -> (result: bool)
    ensures

        (result == true || result == false) &&

        (result == true ==> true) &&

        true &&

        true
// </vc-spec>
// <vc-code>
{
    false
}
// </vc-code>

}
fn main() {}