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
    let a_int: int = a as int;
    let h_int: int = h as int;
    let area_int: int = (a_int * h_int) / 2;
    assert(area_int <= u64::MAX);
    let area = area_int as u64;
    area
}
// </vc-code>

fn main() {}
}