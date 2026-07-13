// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn angle_between_hands(hour: u32, minutes: u32) -> (result: u32)
    requires 
        1 <= hour && hour <= 12,
        minutes <= 59,
    ensures 
        result <= 180,
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