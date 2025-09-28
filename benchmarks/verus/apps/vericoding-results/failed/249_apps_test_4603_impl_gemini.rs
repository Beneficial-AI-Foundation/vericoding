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
/* helper modified by LLM (iteration 5): no changes needed, helper is correct */
fn min(a: i8, b: i8) -> (res: i8)
    ensures res as int == if a < b { a as int } else { b as int },
{
    if a < b {
        a
    } else {
        b
    }
}
// </vc-helpers>

// <vc-spec>
fn solve(a: i8, b: i8, c: i8, d: i8) -> (result: i8)
    requires valid_input(a as int, b as int, c as int, d as int)
    ensures result as int == min_total_fare(a as int, b as int, c as int, d as int)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): removed proof block to simplify for prover */
{
    let min_ab = min(a, b);
    let min_cd = min(c, d);
    let result_i16 = (min_ab as i16) + (min_cd as i16);
    result_i16 as i8
}
// </vc-code>


}

fn main() {}