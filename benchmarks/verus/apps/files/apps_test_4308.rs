// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn valid_input(n: int, k: int) -> bool {
    n >= 1 && k >= 1 && n <= 100 && k <= 100
}

spec fn min_cracker_difference(n: int, k: int) -> int
    recommends k > 0
{
    if n % k == 0 { 0 } else { 1 }
}
// </vc-helpers>

// <vc-spec>
fn solve(n: int, k: int) -> (result: int)
    requires 
        valid_input(n, k)
    ensures 
        result == min_cracker_difference(n, k),
        result == 0 <==> n % k == 0,
        result == 1 <==> n % k != 0
// </vc-spec>
// <vc-code>
{
    // impl-start
    assume(false);
    unreached()
    // impl-end
}
// </vc-code>


}

fn main() {}