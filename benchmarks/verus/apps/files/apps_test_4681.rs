// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn lucas(n: int) -> int
    recommends n >= 0
{
    if n == 0 { 2 }
    else if n == 1 { 1 }
    else { lucas(n-1) + lucas(n-2) }
}

spec fn valid_input(n: int) -> bool {
    1 <= n <= 86
}
// </vc-helpers>

// <vc-spec>
fn solve(n: int) -> (result: int)
    requires valid_input(n)
    ensures result == lucas(n)
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>


}

fn main() {}