// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn valid_input(n: int) -> bool {
    n >= 1
}

spec fn worst_case_presses(n: int) -> int
    recommends valid_input(n)
{
    n * (n * n + 5) / 6
}
// </vc-helpers>

// <vc-spec>
fn solve(n: int) -> (result: int)
    requires valid_input(n),
    ensures result == worst_case_presses(n),
    ensures result >= 1,
// </vc-spec>
// <vc-code>
{
    // impl-start
    assume(false);
    0
    // impl-end
}
// </vc-code>


}

fn main() {}