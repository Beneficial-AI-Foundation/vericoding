// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn valid_input(n: int, d: int) -> bool {
    n >= 1 && n <= 20 && d >= 1 && d <= 20
}

spec fn coverage_range(position: int, d: int) -> (int, int) {
    (position - d, position + d)
}

spec fn trees_covered(n: int, d: int, inspectors: int) -> bool {
    inspectors >= 1 && inspectors <= n && inspectors == ((n - 1) / (2 * d + 1)) + 1
}
// </vc-helpers>

// <vc-spec>
fn min_inspectors(n: int, d: int) -> (result: int)
    requires valid_input(n, d)
    ensures trees_covered(n, d, result)
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>


}

fn main() {}