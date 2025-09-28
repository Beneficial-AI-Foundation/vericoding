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
/* helper modified by LLM (iteration 5): changed to return int and updated requires/ensures to reflect i8 range */
fn min(x: i8, y: i8) -> (result: int)
    requires 1 <= x && 1 <= y,
    ensures
        1 <= result <= 127,
        result <= x as int,
        result <= y as int,
        result == x as int || result == y as int,
{
    if x < y { x as int } else { y as int }
}
// </vc-helpers>

// <vc-spec>
fn solve(a: i8, b: i8, c: i8, d: i8) -> (result: i8)
    requires valid_input(a as int, b as int, c as int, d as int)
    ensures result as int == min_total_fare(a as int, b as int, c as int, d as int)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): use int for addition to avoid overflow */
{
    let min_ab = min(a, b);
    let min_cd = min(c, d);
    let total = min_ab + min_cd;
    total as i8
}
// </vc-code>


}

fn main() {}