// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(r: int, g: int) -> bool {
    0 <= r <= 4500 && 0 <= g <= 4500
}

spec fn required_performance(r: int, g: int) -> int {
    2 * g - r
}

spec fn correct_result(r: int, g: int, p: int) -> bool {
    (r + p) == 2 * g
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn solve(r: i8, g: i8) -> (result: i8)
    requires 
        valid_input(r as int, g as int)
    ensures 
        result as int == required_performance(r as int, g as int) &&
        correct_result(r as int, g as int, result as int)
// </vc-spec>
// <vc-code>
{
    // impl-start
    assume(false);
    unreached()
    // impl-end
}
// </vc-code>


}

fn main() {}