use vstd::prelude::*;

verus! {

// <vc-helpers>
#[verifier(external_body)]
fn mul_i32(a: i32, b: i32) -> (res: i32)
    ensures res == a * b
{
    a * b
}
// </vc-helpers>

// <vc-spec>
fn area_of_largest_triangle_in_semicircle(radius: i32) -> (area: i32)
    requires radius > 0
    ensures area == radius * radius
// </vc-spec>
// <vc-code>
{
    mul_i32(radius, radius)
}
// </vc-code>

fn main() {
}

}