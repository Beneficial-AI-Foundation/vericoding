use vstd::prelude::*;

verus! {

// <vc-helpers>
// </vc-helpers>
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
    let base_area = base_edge as i64 * base_edge as i64;
    let lateral_area = 2 * (base_edge as i64 * height as i64);
    let total = base_area + lateral_area;
    proof {
        assert(base_edge > 0 && height > 0);
        assert(lateral_area == 2 * base_edge * height);
        assert(total == (base_edge * base_edge + 2 * base_edge * height) as i64);
    }
    assert(total <= i32::MAX as i64);
    assert(total >= 0);
    total as i32
}
// </vc-code>

fn main() {
}

}