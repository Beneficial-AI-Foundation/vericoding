// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(n: int) -> bool {
    n >= 3
}

spec fn min_jumps(n: int) -> int
    recommends valid_input(n)
{
    (n - 2) * (n - 2)
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn solve(n: i8) -> (result: i8)
    requires valid_input(n as int)
    ensures result as int == min_jumps(n as int)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): compute in i32 to avoid overflow, then convert to i8 */
    let n32 = n as i32;
    let two32: i32 = 2;
    let n_minus_two32 = n32 - two32;
    let result32 = n_minus_two32 * n_minus_two32;
    let result = result32 as i8;
    result
}
// </vc-code>


}

fn main() {}