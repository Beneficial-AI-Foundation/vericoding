// <vc-preamble>
use vstd::prelude::*;

verus! {
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
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn solve(x: i8, y: i8, z: i8) -> (result: i8)
    requires valid_input(x as int, y as int, z as int)
    ensures valid_solution(x as int, y as int, z as int, result as int)
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>


}

fn main() {}