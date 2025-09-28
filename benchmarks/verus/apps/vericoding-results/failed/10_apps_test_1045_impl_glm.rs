// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(n: int) -> bool {
    n >= 1
}

spec fn cubes_for_level(level: int) -> int
    recommends level >= 1
{
    level * (level + 1) / 2
}

spec fn total_cubes_for_height(h: int) -> int
    recommends h >= 1
{
    h * (h + 1) * (h + 2) / 6
}

spec fn valid_pyramid_height(n: int, h: int) -> bool {
    valid_input(n) && h >= 1 && 
    total_cubes_for_height(h) <= n &&
    total_cubes_for_height(h + 1) > n
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): changed return type to i32 and computation to use i32 to avoid int in non-ghost code */
fn compute_total_cubes(h: i8) -> (total: i32)
    requires h >= 1
    ensures total as int == total_cubes_for_height(h as int)
{
    let h_i32 = h as i32;
    h_i32 * (h_i32 + 1) * (h_i32 + 2) / 6
}

proof fn condition_high_plus_1_is_false(n: int)
    requires valid_input(n)
    ensures total_cubes_for_height(n+1) > n
{
    let lhs = (n+1) * (n+2) * (n+3);
    assert(lhs >= 2*3*4);
    let diff = lhs - 6 * n;
    assert(diff == n * n * n + 6 * n * n + 5 * n + 6);
    assert(n * n * n >= 1);
    assert(6 * n * n >= 6);
    assert(5 * n >= 5);
    assert(diff >= 1 + 6 + 5 + 6);
    assert(1 + 6 + 5 + 6 == 18);
    assert(18 > 0);
}
// </vc-helpers>

// <vc-spec>
fn solve(n: i8) -> (result: i8)
    requires valid_input(n as int)
    ensures 
        result >= 1 &&
        valid_pyramid_height(n as int, result as int)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 2): changed mid computation and condition to use i32 instead of int */
{
    let mut low = 1i8;
    let mut high = n;

    proof {
        condition_high_plus_1_is_false(n as int);
    }

    while low < high
        invariant 
            1 <= low <= high <= n,
            total_cubes_for_height(low as int) <= n as int,
            total_cubes_for_height((high+1) as int) > n as int
        decreases high - low
    {
        let mid = ((low as i32) + (high as i32) + 1) / 2;
        let mid_i8 = mid as i8;

        if compute_total_cubes(mid_i8) <= n as i32 {
            low = mid_i8;
        } else {
            high = mid_i8 - 1;
        }
    }

    low
}
// </vc-code>


}

fn main() {}