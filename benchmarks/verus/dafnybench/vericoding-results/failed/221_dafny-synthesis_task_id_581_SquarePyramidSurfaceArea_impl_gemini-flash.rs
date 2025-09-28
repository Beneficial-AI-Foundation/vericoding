use vstd::prelude::*;

verus! {

// <vc-helpers>
fn integer_square(x: i32) -> (ret: i32)
    requires x >= 0
    ensures ret == x * x
{
    (x as i64 * x as i64) as i32
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
    let base_area = integer_square(base_edge);
    let lateral_area = 2 * base_edge * height;
    base_area + lateral_area
}
// </vc-code>

fn main() {
}

}