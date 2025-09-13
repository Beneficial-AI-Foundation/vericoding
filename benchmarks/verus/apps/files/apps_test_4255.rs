// <vc-preamble>
use vstd::prelude::*;
use vstd::string::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn valid_input(ab: int, bc: int, ca: int) -> bool {
    1 <= ab <= 100 && 1 <= bc <= 100 && 1 <= ca <= 100
}

spec fn triangle_area(ab: int, bc: int) -> int
    recommends ab >= 1 && bc >= 1
{
    (ab * bc) / 2
}

spec fn valid_area(ab: int, bc: int, area: int) -> bool
    recommends ab >= 1 && bc >= 1
{
    area == triangle_area(ab, bc) && area >= 0 && area <= 5000
}
// </vc-helpers>

// <vc-spec>
fn solve(ab: int, bc: int, ca: int) -> (result: String)
    requires valid_input(ab, bc, ca)
    ensures exists|area: int| valid_area(ab, bc, area)
// </vc-spec>
// <vc-code>
{
    // impl-start
    assume(false);
    unreached()
    // impl-end
}
// </vc-code>


}

fn main() {}