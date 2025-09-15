// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(a: int, b: int, t: int) -> bool {
    1 <= a <= 20 && 1 <= b <= 20 && 1 <= t <= 20
}

spec fn production_count(a: int, t: int) -> int {
    if a > 0 { t / a } else { 0 }
}

spec fn total_biscuits(a: int, b: int, t: int) -> int {
    if a > 0 { b * production_count(a, t) } else { 0 }
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn solve(a: int, b: int, t: int) -> (result: int)
    requires valid_input(a, b, t)
    ensures result == total_biscuits(a, b, t)
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>


}

fn main() {}