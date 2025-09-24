// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(n: int, v: int) -> bool {
    2 <= n <= 100 && 1 <= v <= 100
}

spec fn min_cost(n: int, v: int) -> int {
    let req = n - 1;
    if req <= v {
        req
    } else {
        let remaining = req - v;
        v + remaining * (remaining + 3) / 2
    }
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn solve(n: i8, v: i8) -> (result: i8)
    requires valid_input(n as int, v as int)
    ensures result as int == min_cost(n as int, v as int)
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>


}

fn main() {}