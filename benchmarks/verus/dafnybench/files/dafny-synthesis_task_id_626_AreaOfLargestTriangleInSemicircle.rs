// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn area_of_largest_triangle_in_semicircle(radius: i8) -> (area: i8)
    requires radius > 0
    ensures area as int == radius as int * radius as int
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}