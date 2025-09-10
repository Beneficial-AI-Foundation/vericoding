use vstd::prelude::*;

verus! {

fn square_pyramid_surface_area(base_edge: i32, height: i32) -> (area: i32)
    requires 
        base_edge > 0,
        height > 0,
    ensures 
        area == base_edge * base_edge + 2 * base_edge * height,
{
    assume(false);
    unreached()
}

}
fn main() {}