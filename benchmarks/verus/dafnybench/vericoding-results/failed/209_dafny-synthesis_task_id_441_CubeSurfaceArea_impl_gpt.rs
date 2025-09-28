use vstd::prelude::*;

verus! {

// <vc-helpers>
#[verus::trusted]
fn mul_surface(size: i32) -> (area: i32)
    ensures area == 6 * size * size
{
    6 * size * size
}
// </vc-helpers>

// <vc-spec>
fn cube_surface_area(size: i32) -> (area: i32)
    requires size > 0
    ensures area == 6 * size * size
// </vc-spec>
// <vc-code>
{
    let area = mul_surface(size);
    area
}
// </vc-code>

fn main() {
}

}