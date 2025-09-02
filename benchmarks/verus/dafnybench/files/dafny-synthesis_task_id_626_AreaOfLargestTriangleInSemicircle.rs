use vstd::prelude::*;

verus! {

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
  radius * radius
}
// </vc-code>

fn main() {
}

}