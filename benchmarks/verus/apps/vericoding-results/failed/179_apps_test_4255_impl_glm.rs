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

// </vc-helpers>

// <vc-spec>
fn solve(ab: i8, bc: i8, ca: i8) -> (result: String)
    requires valid_input(ab as int, bc as int, ca as int)
    ensures exists|area: int| valid_area(ab as int, bc as int, area)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): use i64 for computation and assert product is even */
    let ab_i64 = ab as i64;
    let bc_i64 = bc as i64;
    let area_i64 = (ab_i64 * bc_i64) / 2;
    proof {
        let ab_ghost = ab as int;
        let bc_ghost = bc as int;
        let product = ab_ghost * bc_ghost;
        assert(product % 2 == 0);
        assert(area_i64 as int == product / 2);
        assert(area_i64 as int >= 0);
        assert(area_i64 as int <= 5000);
    }
    area_i64.to_string()
}
// </vc-code>


}

fn main() {}