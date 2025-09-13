// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn valid_input(a: int, b: int) -> bool {
    1 <= a <= 100 && 1 <= b <= 100
}

spec fn uncovered_length(a: int, b: int) -> int {
    if a - 2 * b > 0 { a - 2 * b } else { 0 }
}
// </vc-helpers>

// <vc-spec>
fn solve(a: int, b: int) -> (result: int)
    requires 
        valid_input(a, b)
    ensures 
        result >= 0,
        result == uncovered_length(a, b),
        result == if a > 2 * b { a - 2 * b } else { 0 }
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>


}

fn main() {}