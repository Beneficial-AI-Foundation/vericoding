use vstd::prelude::*;

verus! {

// <vc-helpers>
//
// </vc-helpers>

// <vc-spec>
fn cylinder_lateral_surface_area(radius: u64, height: u64) -> (area: u64)
    requires 
        radius > 0,
        height > 0,
    ensures area == 2 * radius * height * 314 / 100,
// </vc-spec>
// <vc-code>
{
    let math_area = 2 * (radius as int) * (height as int) * 314 / 100;
    let computed_area = 2u64 * radius * height * 314u64 / 100u64;
    let computed_area_int = computed_area as int;
    proof {
        assert(computed_area_int == math_area);
    }
    computed_area
}
// </vc-code>

fn main() {
}

}