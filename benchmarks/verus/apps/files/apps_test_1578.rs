// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn valid_input(n: int) -> bool {
    n >= 1
}

spec fn max_sum(n: int) -> int
    recommends n >= 1
{
    n * (n - 1) / 2
}
// </vc-helpers>

// <vc-spec>
fn solve(n: int) -> (result: int)
    requires valid_input(n)
    ensures result == max_sum(n)
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>


}

fn main() {}