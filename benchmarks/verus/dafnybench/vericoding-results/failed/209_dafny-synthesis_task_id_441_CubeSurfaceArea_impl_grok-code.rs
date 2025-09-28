use vstd::prelude::*;

verus! {

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn cube_surface_area(size: i32) -> (area: i32)
    requires size > 0
    ensures area == 6 * size * size
// </vc-spec>
// <vc-code>
{
    let res = 6 * size * size;
    assert(res == 6 * size * size);
    return res;
}
// </vc-code>

fn main() {
}

}