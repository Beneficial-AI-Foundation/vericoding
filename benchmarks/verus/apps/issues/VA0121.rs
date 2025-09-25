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
fn solve(x: i8, y: i8, z: i8) -> (result: (i8, i8))
    requires valid_input(x as int, y as int, z as int)
    ensures result.0 as int == max_coconuts(x as int, y as int, z as int) && result.1 as int == min_exchange(x as int, y as int, z as int) && result.0 as int >= (x as int) / (z as int) + (y as int) / (z as int) && result.0 as int <= (x as int) / (z as int) + (y as int) / (z as int) + 1 && result.1 as int >= 0 && result.1 as int < (z as int)
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>


}

fn main() {}