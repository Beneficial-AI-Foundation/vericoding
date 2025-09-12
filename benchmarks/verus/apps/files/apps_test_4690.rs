// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn valid_input(a: int, b: int, c: int, d: int) -> bool {
    1 <= a <= 10000 && 1 <= b <= 10000 && 1 <= c <= 10000 && 1 <= d <= 10000
}

spec fn max_area(a: int, b: int, c: int, d: int) -> int {
    if a * b >= c * d { a * b } else { c * d }
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn solve(a: int, b: int, c: int, d: int) -> (result: int)
    requires 
        valid_input(a, b, c, d)
    ensures 
        result == max_area(a, b, c, d),
        result >= a * b && result >= c * d,
        result == a * b || result == c * d
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>


}

fn main() {}