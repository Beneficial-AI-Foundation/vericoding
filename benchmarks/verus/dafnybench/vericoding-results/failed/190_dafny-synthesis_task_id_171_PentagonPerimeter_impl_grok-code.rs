use vstd::prelude::*;

verus! {

// <vc-helpers>
use vstd::math::*;
use vstd::arithmetic::power::pow;
// </vc-helpers>

// <vc-spec>
fn pentagon_perimeter(side: i32) -> (perimeter: i32)
    requires side > 0
    ensures perimeter == 5 * side
// </vc-spec>
// <vc-code>
{
    assert(side@ as int <= (pow(2, 31) - 1) / 5);
    5 * side
}
// </vc-code>

fn main() {
}

}