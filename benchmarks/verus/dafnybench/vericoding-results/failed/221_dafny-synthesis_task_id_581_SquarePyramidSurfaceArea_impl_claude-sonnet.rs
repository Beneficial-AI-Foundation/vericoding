use vstd::prelude::*;

verus! {

// <vc-helpers>
proof fn lemma_square_fits_i32(base_edge: i32)
    requires base_edge > 0 && base_edge <= 46340
    ensures base_edge * base_edge <= i32::MAX
{
}

proof fn lemma_double_fits_i32(base_edge: i32)
    requires base_edge > 0 && base_edge <= i32::MAX / 2
    ensures 2 * base_edge <= i32::MAX
{
}

proof fn lemma_lateral_area_fits_i32(base_edge: i32, height: i32)
    requires 
        base_edge > 0 && height > 0,
        base_edge <= i32::MAX / 2,
        height <= i32::MAX / (2 * base_edge)
    ensures 2 * base_edge * height <= i32::MAX
{
}
// </vc-helpers>

// <vc-spec>
fn square_pyramid_surface_area(base_edge: i32, height: i32) -> (area: i32)
    requires 
        base_edge > 0,
        height > 0,
    ensures 
        area == base_edge * base_edge + 2 * base_edge * height,
// </vc-spec>
// <vc-code>
{
    let base_area = base_edge * base_edge;
    let lateral_area = 2 * base_edge * height;
    base_area + lateral_area
}
// </vc-code>

fn main() {
}

}