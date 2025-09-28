use vstd::prelude::*;

verus! {

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn pentagon_perimeter(side: i32) -> (perimeter: i32)
    requires side > 0
    ensures perimeter == 5 * side
// </vc-spec>
// <vc-code>
{
    assert(side > 0);
    assert(side <= i32::MAX / 5);
    5 * side
}
// </vc-code>

fn main() {
}

}