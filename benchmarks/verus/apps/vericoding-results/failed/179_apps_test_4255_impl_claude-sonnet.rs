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
/* helper modified by LLM (iteration 5): strengthen bounds proof and add checked_mul lemma */
proof fn area_bounds_lemma(ab: int, bc: int)
    requires 1 <= ab <= 100, 1 <= bc <= 100
    ensures triangle_area(ab, bc) <= 5000
{
    assert(ab <= 100 && bc <= 100);
    assert(ab * bc <= 100 * 100) by {
        assert(ab <= 100);
        assert(bc <= 100);
    };
    assert(ab * bc <= 10000);
    assert((ab * bc) / 2 <= 5000);
}

proof fn checked_mul_success_lemma(ab: i8, bc: i8)
    requires 1 <= ab <= 100, 1 <= bc <= 100
    ensures (ab as i32).checked_mul(bc as i32).is_some()
{
    assert(ab as i32 <= 100);
    assert(bc as i32 <= 100);
    assert((ab as i32) * (bc as i32) <= 10000);
    assert(10000 <= 2147483647);
}
// </vc-helpers>

// <vc-spec>
fn solve(ab: i8, bc: i8, ca: i8) -> (result: String)
    requires valid_input(ab as int, bc as int, ca as int)
    ensures exists|area: int| valid_area(ab as int, bc as int, area)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): add checked_mul success proof */
    proof {
        checked_mul_success_lemma(ab, bc);
    }
    let area_exec = ((ab as i32).checked_mul(bc as i32).unwrap()) / 2;
    proof {
        let ghost area_ghost = ab as int * bc as int / 2;
        area_bounds_lemma(ab as int, bc as int);
        assert(area_ghost == triangle_area(ab as int, bc as int));
        assert(area_ghost >= 0);
        assert(area_ghost <= 5000);
        assert(valid_area(ab as int, bc as int, area_ghost));
        assert(area_exec == area_ghost);
    }
    area_exec.to_string()
}
// </vc-code>


}

fn main() {}