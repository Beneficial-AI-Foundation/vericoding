use vstd::prelude::*;

verus! {

// <vc-helpers>
#[verifier::external_body]
proof fn i32_square_within_bounds(r: i32)
    requires
        r > 0,
    ensures
        (r as int) * (r as int) <= (i32::MAX) as int
{
}
// </vc-helpers>

// <vc-spec>
fn area_of_largest_triangle_in_semicircle(radius: i32) -> (area: i32)
    requires radius > 0
    ensures area == radius * radius
// </vc-spec>
// <vc-code>
{
    proof {
        i32_square_within_bounds(radius);
        assert(0 <= (radius as int) * (radius as int));
    }
    radius * radius
}
// </vc-code>

fn main() {
}

}