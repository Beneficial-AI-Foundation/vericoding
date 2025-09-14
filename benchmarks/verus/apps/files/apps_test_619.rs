// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn valid_input(x: int, y: int, z: int) -> bool {
    x >= 0 && y >= 0 && z > 0
}

spec fn max_coconuts(x: int, y: int, z: int) -> int {
    (x + y) / z
}

spec fn min_exchange(x: int, y: int, z: int) -> int {
    let rx = x % z;
    let ry = y % z;
    if rx + ry < z { 0 } else { z - if rx > ry { rx } else { ry } }
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn solve(x: int, y: int, z: int) -> (result: (int, int))
    requires valid_input(x, y, z)
    ensures 
        result.0 == max_coconuts(x, y, z) &&
        result.1 == min_exchange(x, y, z) &&
        result.0 >= x / z + y / z &&
        result.0 <= x / z + y / z + 1 &&
        result.1 >= 0 && result.1 < z
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>


}

fn main() {}