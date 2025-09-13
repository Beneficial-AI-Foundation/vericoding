// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn alternating_sum(n: int) -> int
    recommends n > 0
    decreases n
{
    if n == 1 { -1 }
    else { alternating_sum(n-1) + (if n % 2 == 0 { n } else { -n }) }
}

spec fn valid_input(n: int) -> bool {
    n > 0
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn solve(n: int) -> (result: int)
    requires valid_input(n)
    ensures 
        result == alternating_sum(n) &&
        (n % 2 == 0 ==> result == n / 2) &&
        (n % 2 != 0 ==> result == n / 2 - n)
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>


}

fn main() {}