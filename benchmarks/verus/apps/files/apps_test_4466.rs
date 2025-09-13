// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn valid_input(x: int, y: int, z: int) -> bool {
    x >= 1 && y >= 1 && z >= 1 && y + 2 * z <= x
}

spec fn max_people(x: int, y: int, z: int) -> int
    recommends valid_input(x, y, z)
{
    (x - z) / (y + z)
}

spec fn valid_solution(x: int, y: int, z: int, result: int) -> bool
    recommends valid_input(x, y, z)
{
    result == max_people(x, y, z) &&
    result >= 0 &&
    result * (y + z) <= x - z < (result + 1) * (y + z)
}
// </vc-helpers>

// <vc-spec>
fn solve(x: int, y: int, z: int) -> (result: int)
    requires valid_input(x, y, z)
    ensures valid_solution(x, y, z, result)
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>


}

fn main() {}