// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(n: int) -> bool {
    1 <= n <= 10000
}

spec fn valid_change(change: int) -> bool {
    0 <= change <= 999
}

spec fn correct_change(n: int) -> int
    recommends valid_input(n)
{
    (1000 - n % 1000) % 1000
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn solve(n: int) -> (change: int)
    requires valid_input(n)
    ensures 
        valid_change(change) &&
        change == correct_change(n)
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>


}

fn main() {}