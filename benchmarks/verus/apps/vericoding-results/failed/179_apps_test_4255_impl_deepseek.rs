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
/* helper modified by LLM (iteration 5): Add missing proof helpers for division properties and bounds */
proof fn nonnegative_div_proof(a: int, b: int)
    requires
        a >= 0,
        b > 0,
    ensures
        (a * b) / 2 >= 0,
{
    // Division of non-negative values results in non-negative value
}

proof fn div_le_proof(numerator: int, max_factor1: int, max_factor2: int)
    requires
        numerator >= 0,
        max_factor1 >= 1,
        max_factor2 >= 1,
    ensures
        numerator / 2 <= max_factor1 * max_factor2 / 2,
{
    // Proof that division preserves ordering relationship
}
// </vc-helpers>

// <vc-spec>
fn solve(ab: i8, bc: i8, ca: i8) -> (result: String)
    requires valid_input(ab as int, bc as int, ca as int)
    ensures exists|area: int| valid_area(ab as int, bc as int, area)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Simplified implementation with proper area calculation */
{
    proof {
        let area_int = (ab as int * bc as int) / 2;
        assert(area_int >= 0) by {
            assert(ab as int >= 1 && bc as int >= 1);
        }
        assert(area_int <= 5000) by {
            assert(ab as int <= 100 && bc as int <= 100);
            assert(ab as int * bc as int <= 100 * 100);
        }
        assert(area_int == triangle_area(ab as int, bc as int));
    }
    
    let area = (ab as i32 * bc as i32) / 2;
    format!("{}", area)
}
// </vc-code>


}

fn main() {}