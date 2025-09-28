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
spec fn compute_area(a: int, b: int) -> int
    requires
        a >= 1,
        b >= 1
    ensures
        result == (a * b) / 2
{
    (a * b) / 2
}
// </vc-helpers>

// <vc-spec>
fn solve(ab: i8, bc: i8, ca: i8) -> (result: String)
    requires valid_input(ab as int, bc as int, ca as int)
    ensures exists|area: int| valid_area(ab as int, bc as int, area)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5):  */
    let a32 = ab as i32;
    let b32 = bc as i32;
    let prod = a32 as i64 * b32 as i64;
    let area_exe = (prod / 2) as i32;
    let string_area = format!("{}", area_exe);
    proof {
        assert(area_exe as int == triangle_area(ab as int, bc as int));
        assert(valid_area(ab as int, bc as int, area_exe as int));
    }
    string_area
}
// </vc-code>


}

fn main() {}