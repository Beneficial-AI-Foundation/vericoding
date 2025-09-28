// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(a: int, b: int, c: int, d: int) -> bool {
    1 <= a <= 1000 && 1 <= b <= 1000 && 1 <= c <= 1000 && 1 <= d <= 1000
}

spec fn min_total_fare(a: int, b: int, c: int, d: int) -> int {
    (if a < b { a } else { b }) + (if c < d { c } else { d })
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Define proper min function with explicit int returns */
spec fn min(x: int, y: int) -> int {
    if x < y {
        x
    } else {
        y
    }
}
// </vc-helpers>

// <vc-spec>
fn solve(a: i8, b: i8, c: i8, d: i8) -> (result: i8)
    requires valid_input(a as int, b as int, c as int, d as int)
    ensures result as int == min_total_fare(a as int, b as int, c as int, d as int)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Fixed compilation error by using proper syntax */
{
    let min_ab = (if a < b { a } else { b }) as int;
    let min_cd = (if c < d { c } else { d }) as int;
    let result = (min_ab + min_cd) as i8;
    result
}
// </vc-code>


}

fn main() {}