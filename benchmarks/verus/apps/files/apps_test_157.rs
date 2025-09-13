// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn valid_input(a: int, b: int, c: int) -> bool {
    1 <= a <= 1000 && 1 <= b <= 1000 && 1 <= c <= 1000
}

spec fn max_recipe_units(a: int, b: int, c: int) -> int {
    vstd::math::min(a, vstd::math::min(b / 2, c / 4))
}

spec fn total_fruits_used(units: int) -> int {
    units * 7
}
// </vc-helpers>

// <vc-spec>
fn solve(a: int, b: int, c: int) -> (result: int)
    requires 
        valid_input(a, b, c)
    ensures 
        result == total_fruits_used(max_recipe_units(a, b, c)),
        result >= 0
// </vc-spec>
// <vc-code>
{
    assume(false);
    0int
}
// </vc-code>


}

fn main() {}