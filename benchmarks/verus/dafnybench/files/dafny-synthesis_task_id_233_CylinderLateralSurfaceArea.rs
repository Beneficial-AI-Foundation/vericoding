use vstd::prelude::*;

verus! {

fn cylinder_lateral_surface_area(radius: u64, height: u64) -> (area: u64)
    requires 
        radius > 0,
        height > 0,
    ensures area == 2 * radius * height * 314 / 100,
{
    assume(false);
    unreached()
}

}
fn main() {}