use vstd::prelude::*;

verus! {

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn triangle_area(a: u64, h: u64) -> (area: u64)
    // pre-conditions-start
    requires
        a > 0,
        h > 0,
        a * h / 2 <= u64::MAX
        ,
    // pre-conditions-end
    // post-conditions-start
    ensures
        area == a * h / 2,
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
    proof {
        let expected_area: int = (a as int * h as int) / 2;
    }
    let intermediate: u128 = a as u128 * h as u128;
    let area_inter: u128 = intermediate / 2;
    proof {
        assert((intermediate / 2) as int == expected_area);
        assert(area_inter <= u64::MAX as u128);
    }
    let area = area_inter as u64;
    area
}
// </vc-code>

fn main() {}
}