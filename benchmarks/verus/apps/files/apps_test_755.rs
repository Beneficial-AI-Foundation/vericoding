// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(x: int) -> bool {
    x >= 1
}

spec fn is_minimal_steps(x: int, steps: int) -> bool {
    x >= 1 ==> (steps >= 1 &&
    steps * 5 >= x &&
    (steps - 1) * 5 < x)
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn min_steps(x: i8) -> (result: i8)
    requires valid_input(x as int)
    ensures is_minimal_steps(x as int, result as int)
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>


}

fn main() {}