use vstd::prelude::*;

verus! {

// <vc-helpers>
use vstd::prelude::*;

proof fn mul_commutative(a: u64, b: u64)
    ensures a * b == b * a
{
}

proof fn mul_distributive(a: u64, b: u64, c: u64)
    ensures a * (b + c) == a * b + a * c
{
}
// </vc-helpers>

// <vc-spec>
// <vc-spec>
fn cylinder_surface_area(radius: u64, height: u64) -> (area: u64)
    requires radius > 0 && height > 0
    ensures area == 2 * radius * (radius + height)
// </vc-spec>
// </vc-spec>

// <vc-code>
fn cylinder_surface_area(radius: u64, height: u64) -> (area: u64)
    requires radius > 0 && height > 0
    ensures area == 2 * radius * (radius + height)
{
    let base_area = radius * radius;
    let lateral_area = 2 * radius * height;
    let total_area = 2 * base_area + lateral_area;
    total_area
}
// </vc-code>

fn main() {}

}