// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn valid_input(x: int, y: int, z: int) -> bool {
    x >= 0 && y >= 0 && z > 0
}

spec fn max_coconuts(x: int, y: int, z: int) -> int
    requires valid_input(x, y, z)
{
    (x + y) / z
}

spec fn min_exchange(x: int, y: int, z: int) -> int
    requires valid_input(x, y, z)
{
    let rx = x % z;
    let ry = y % z;
    if rx + ry < z { 0 }
    else { z - if rx > ry { rx } else { ry } }
}
// </vc-helpers>

// <vc-spec>
fn solve(x: int, y: int, z: int) -> (result: (int, int))
    requires valid_input(x, y, z)
    ensures ({
        let (coconuts, exchange) = result;
        coconuts == max_coconuts(x, y, z) &&
        exchange == min_exchange(x, y, z) &&
        coconuts >= x / z + y / z &&
        coconuts <= x / z + y / z + 1 &&
        exchange >= 0 && exchange < z
    })
// </vc-spec>
// <vc-code>
{
    // impl-start
    assume(false);
    (0, 0)
    // impl-end
}
// </vc-code>


}

fn main() {}