// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(n: int, d: int) -> bool {
    n >= 1 && n <= 20 && d >= 1 && d <= 20
}

spec fn coverage_range(position: int, d: int) -> (int, int) {
    (position - d, position + d)
}

spec fn trees_covered(n: int, d: int, inspectors: int) -> bool {
    inspectors >= 1 && inspectors <= n && inspectors == ((n - 1) / (2 * d + 1)) + 1
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn min_inspectors(n: i8, d: i8) -> (result: i8)
    requires valid_input(n as int, d as int)
    ensures trees_covered(n as int, d as int, result as int)
// </vc-spec>
// <vc-code>
{
    let coverage_diameter = 2 * d + 1;
    let result = ((n - 1) / coverage_diameter) + 1;
    result
}
// </vc-code>


}

fn main() {}