// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(n: int) -> bool {
    n >= 3
}

spec fn min_jumps(n: int) -> int
    recommends valid_input(n)
{
    (n - 2) * (n - 2)
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn solve(n: i8) -> (result: i8)
    requires valid_input(n as int)
    ensures result as int == min_jumps(n as int)
// </vc-spec>
// <vc-code>
{
/* code modified by LLM (iteration 4): compute diff and jumps using i8 to avoid int in exec code, with proof assertion */
    let diff: i8 = n - 2;
    let jumps: i8 = diff * diff;
    proof {
        assert(diff == (n as int) - 2);
        assert(jumps == min_jumps(n as int));
    }
    jumps
}
// </vc-code>


}

fn main() {}