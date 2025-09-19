// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn alternating_sum(n: int) -> int
    recommends n > 0
    decreases n
{
    if n <= 0 { 0 }
    else if n == 1 { -1 }
    else { alternating_sum(n - 1) + (if n % 2 == 0 { n } else { -n }) }
}

spec fn valid_input(n: int) -> bool {
    n > 0
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn solve(n: i8) -> (result: i8)
    requires valid_input(n as int)
    ensures 
        result as int == alternating_sum(n as int) &&
        (n as int % 2 == 0 ==> result as int == n as int / 2) &&
        (n as int % 2 != 0 ==> result as int == n as int / 2 - n as int)
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>


}

fn main() {}