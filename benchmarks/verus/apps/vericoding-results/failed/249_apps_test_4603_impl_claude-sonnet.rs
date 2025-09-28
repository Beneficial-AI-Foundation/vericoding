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
fn min(x: i8, y: i8) -> (result: i8)
    ensures result as int == (if x < y { x as int } else { y as int })
{
    if x < y { x } else { y }
}
// </vc-helpers>

// <vc-spec>
fn solve(a: i8, b: i8, c: i8, d: i8) -> (result: i8)
    requires valid_input(a as int, b as int, c as int, d as int)
    ensures result as int == min_total_fare(a as int, b as int, c as int, d as int)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): compute min values and add directly as i8 */
    let min_ab = min(a, b);
    let min_cd = min(c, d);
    proof {
        assert(min_ab as int >= 1 && min_ab as int <= 1000);
        assert(min_cd as int >= 1 && min_cd as int <= 1000);
        assert(min_ab as int + min_cd as int >= 2 && min_ab as int + min_cd as int <= 2000);
        assert(min_ab as int + min_cd as int <= 127);
    }
    let result = min_ab + min_cd;
    result
}
// </vc-code>


}

fn main() {}