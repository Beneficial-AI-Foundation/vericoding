// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(r: int, g: int, b: int) -> bool {
    r >= 0 && g >= 0 && b >= 0
}

spec fn max_tables(r: int, g: int, b: int) -> int
    recommends valid_input(r, g, b)
{
    min(min(min((r + g + b) / 3, r + g), r + b), g + b)
}

spec fn min(a: int, b: int) -> int {
    if a <= b { a } else { b }
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn solve(r: i8, g: i8, b: i8) -> (result: i8)
    requires 
        valid_input(r as int, g as int, b as int)
    ensures 
        result as int == max_tables(r as int, g as int, b as int),
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