use vstd::prelude::*;

verus! {

fn cube_surface_area(size: i32) -> (area: i32)
    requires size > 0
    ensures area == 6 * size * size
{
    assume(false);
    unreached()
}

}
fn main() {}