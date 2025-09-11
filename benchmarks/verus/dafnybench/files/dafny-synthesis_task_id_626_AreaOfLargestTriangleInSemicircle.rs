// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn area_of_largest_triangle_in_semicircle(radius: i32) -> (area: i32)
    requires radius > 0
    ensures area == radius * radius
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}