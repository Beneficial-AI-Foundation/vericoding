use vstd::prelude::*;

verus! {

// <vc-helpers>
// No helpers needed for this task.
// </vc-helpers>

// <vc-spec>
fn cube_surface_area(size: i32) -> (area: i32)
    requires size > 0
    ensures area == 6 * size * size
// </vc-spec>
// <vc-code>
{
    let area: i32 = 6 * size * size;
    proof {
        let s_int: int = size as int;
        let area_int: int = 6 * s_int * s_int;
        assert((area as int) == area_int);
    }
    area
}
// </vc-code>

fn main() {
}

}