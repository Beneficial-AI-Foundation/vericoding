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
fn solve(r: int, g: int) -> (result: int)
    requires 
        valid_input(r, g)
    ensures 
        result == required_performance(r, g) &&
        correct_result(r, g, result)
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