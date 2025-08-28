use vstd::prelude::*;

verus! {

// <vc-helpers>
// No updates needed for helpers as the issue was a syntax error in the code section
// </vc-helpers>

// <vc-spec>
// <vc-spec>
fn square_pyramid_surface_area(base_edge: i32, height: i32) -> (area: i32)
    requires 
        base_edge > 0,
        height > 0,
    ensures 
        area == base_edge * base_edge + 2 * base_edge * height,
// </vc-spec>
// </vc-spec>

// <vc-code>
fn square_pyramid_surface_area(base_edge: i32, height: i32) -> (area: i32)
    requires
        base_edge > 0,
        height > 0,
    ensures
        area == base_edge * base_edge + 2 * base_edge * height,
{
    let base_area = base_edge * base_edge;
    let lateral_area = 2 * base_edge * height;
    let area = base_area + lateral_area;
    area
}
// </vc-code>

fn main() {
}

}