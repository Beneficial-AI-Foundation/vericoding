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
fn solve(r: int, g: int, b: int) -> (result: int)
    requires 
        valid_input(r, g, b)
    ensures 
        result == max_tables(r, g, b),
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