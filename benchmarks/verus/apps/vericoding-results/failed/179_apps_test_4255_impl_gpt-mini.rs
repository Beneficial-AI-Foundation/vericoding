// <vc-preamble>
use vstd::prelude::*;
use vstd::string::*;

verus! {
spec fn valid_input(ab: int, bc: int, ca: int) -> bool {
    1 <= ab <= 100 && 1 <= bc <= 100 && 1 <= ca <= 100
}

spec fn triangle_area(ab: int, bc: int) -> int
    recommends ab >= 1 && bc >= 1
{
    (ab * bc) / 2
}

spec fn valid_area(ab: int, bc: int, area: int) -> bool
    recommends ab >= 1 && bc >= 1
{
    area == triangle_area(ab, bc) && area >= 0 && area <= 5000
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): proves triangle_area bounds */
proof fn triangle_area_bounds(ab: int, bc: int)
    requires
        1 <= ab <= 100,
        1 <= bc <= 100,
    ensures
        triangle_area(ab, bc) >= 0,
        triangle_area(ab, bc) <= 5000,
{
    assert(triangle_area(ab, bc) == (ab * bc) / 2);
    assert(ab * bc <= 100 * 100);
    assert((ab * bc) / 2 <= 5000);
    assert((ab * bc) / 2 >= 0);
}

// </vc-helpers>

// <vc-spec>
fn solve(ab: i8, bc: i8, ca: i8) -> (result: String)
    requires valid_input(ab as int, bc as int, ca as int)
    ensures exists|area: int| valid_area(ab as int, bc as int, area)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): compute area and prove valid_area */
    let ab_i32: i32 = ab as i32;
    let bc_i32: i32 = bc as i32;
    let area_i32: i32 = (ab_i32 * bc_i32) / 2;
    let result = area_i32.to_string();

    proof {
        let ab_i: int = ab as int;
        let bc_i: int = bc as int;
        let area_i: int = area_i32 as int;
        triangle_area_bounds(ab_i, bc_i);
        assert(ab_i32 as int == ab_i);
        assert(bc_i32 as int == bc_i);
        assert(((ab_i32 * bc_i32) / 2) as int == (ab_i * bc_i) / 2);
        assert(((ab_i32 * bc_i32) / 2) as int == area_i);
        assert(triangle_area(ab_i, bc_i) == area_i);
        assert(valid_area(ab_i, bc_i, area_i));
    }
    result
}
// </vc-code>


}

fn main() {}