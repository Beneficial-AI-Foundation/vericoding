// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn valid_input(n: int, m: int, a: int, b: int) -> bool {
    n >= 1 && m >= 1 && a >= 1 && b >= 1
}

spec fn min_cost_to_divisible(n: int, m: int, a: int, b: int) -> int
    requires valid_input(n, m, a, b)
{
    let k = n % m;
    if k * b < (m - k) * a { k * b } else { (m - k) * a }
}
// </vc-helpers>

// <vc-spec>
fn solve(n: int, m: int, a: int, b: int) -> (result: int)
    requires 
        valid_input(n, m, a, b)
    ensures 
        result == min_cost_to_divisible(n, m, a, b),
        result >= 0,
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>


}

fn main() {}