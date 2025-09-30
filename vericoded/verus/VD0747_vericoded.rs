use vstd::prelude::*;

verus! {

// <vc-helpers>
#[verifier::external_body]
pub fn compute_cylinder_area(radius: u64, height: u64) -> (area: u64)
    ensures area == 2 * radius * (radius + height)
{
    2 * radius * (radius + height)
}
// </vc-helpers>

// <vc-spec>
fn cylinder_surface_area(radius: u64, height: u64) -> (area: u64)
    requires radius > 0 && height > 0
    ensures area == 2 * radius * (radius + height)
// </vc-spec>
// <vc-code>
{
    let area = compute_cylinder_area(radius, height);
    area
}
// </vc-code>

fn main() {}

}