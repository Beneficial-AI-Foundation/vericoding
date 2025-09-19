// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn valid_input(a: int, b: int, c: int) -> bool {
    1 <= a <= 1000 && 1 <= b <= 1000 && 1 <= c <= 1000
}

spec fn max_recipe_units(a: int, b: int, c: int) -> int {
    if a <= b / 2 && a <= c / 4 {
        a
    } else if b / 2 <= a && b / 2 <= c / 4 {
        b / 2
    } else {
        c / 4
    }
}

spec fn total_fruits_used(units: int) -> int {
    units * 7
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn solve(a: i8, b: i8, c: i8) -> (result: i8)
    requires 
        valid_input(a as int, b as int, c as int)
    ensures 
        result as int == total_fruits_used(max_recipe_units(a as int, b as int, c as int)),
        result >= 0
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>


}

fn main() {}