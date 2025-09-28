// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn max(a: int, b: int) -> int {
    if a >= b { a } else { b }
}

spec fn valid_input(a: int, b: int, x: int, y: int, z: int) -> bool {
    a >= 0 && b >= 0 && x >= 0 && y >= 0 && z >= 0
}

spec fn yellow_crystals_needed(x: int, y: int) -> int {
    x * 2 + y
}

spec fn blue_crystals_needed(y: int, z: int) -> int {
    y + z * 3
}

spec fn min_additional_crystals(a: int, b: int, x: int, y: int, z: int) -> int {
    max(0, yellow_crystals_needed(x, y) - a) + max(0, blue_crystals_needed(y, z) - b)
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): removed helper - not needed */
// </vc-helpers>

// <vc-spec>
fn solve(a: i8, b: i8, x: i8, y: i8, z: i8) -> (result: i8)
    requires 
        valid_input(a as int, b as int, x as int, y as int, z as int)
    ensures 
        result >= 0,
        result as int == min_additional_crystals(a as int, b as int, x as int, y as int, z as int)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): corrected type casting errors and added intermediate `ghost` variables */
    let yellow_needed_spec: ghost int = yellow_crystals_needed(x as int, y as int);
    let blue_needed_spec: ghost int = blue_crystals_needed(y as int, z as int);

    let additional_yellow_spec: ghost int = max(0, yellow_needed_spec - (a as int));
    let additional_blue_spec: ghost int = max(0, blue_needed_spec - (b as int));

    let result_spec: ghost int = additional_yellow_spec + additional_blue_spec;

    // Direct computation using i64 types to avoid overflow during intermediate steps.
    let yellow_needed_i64: i64 = (x as i64) * 2 + (y as i64);
    let blue_needed_i64: i64 = (y as i64) + (z as i64) * 3;

    let additional_yellow_i64: i64 = if yellow_needed_i64 > (a as i64) { yellow_needed_i64 - (a as i64) } else { 0 };
    let additional_blue_i64: i64 = if blue_needed_i64 > (b as i64) { blue_needed_i64 - (b as i64) } else { 0 };

    let result_i64 = additional_yellow_i64 + additional_blue_i64;

    proof {
        assert(yellow_needed_i64 == yellow_needed_spec);
        assert(blue_needed_i64 == blue_needed_spec);
        assert(additional_yellow_i64 == additional_yellow_spec);
        assert(additional_blue_i64 == additional_blue_spec);
        assert(result_i64 == result_spec);

        assert(result_i64 <= i8::MAX as i64);
        assert(result_i64 >= 0);
    }

    result_i64 as i8
}
// </vc-code>


}

fn main() {}