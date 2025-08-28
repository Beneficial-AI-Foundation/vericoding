use vstd::prelude::*;

verus! {

// <vc-helpers>
spec fn valid_pentagon_side(side: i32) -> bool {
    side > 0 && side <= i32::MAX / 5
}
// </vc-helpers>

// <vc-spec>
// <vc-spec>
fn pentagon_perimeter(side: i32) -> (perimeter: i32)
    requires side > 0
    ensures perimeter == 5 * side
// </vc-spec>
// </vc-spec>

// <vc-code>
{
    5i32 * side
}
// </vc-code>

fn main() {
}

}