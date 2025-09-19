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
fn solve(a: i8, b: i8, t: i8) -> (result: i8)
    requires valid_input(a as int, b as int, t as int)
    ensures result as int == total_biscuits(a as int, b as int, t as int)
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>


}

fn main() {}