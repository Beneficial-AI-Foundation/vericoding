// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn valid_input(H: int, W: int, h: int, w: int) -> bool {
    1 <= H <= 20 && 1 <= W <= 20 && 1 <= h <= H && 1 <= w <= W
}

spec fn white_cells_remaining(H: int, W: int, h: int, w: int) -> int 
    recommends valid_input(H, W, h, w)
{
    (H - h) * (W - w)
}
// </vc-helpers>

// <vc-spec>
fn solve(H: int, W: int, h: int, w: int) -> (result: int)
    requires 
        valid_input(H, W, h, w)
    ensures 
        result == white_cells_remaining(H, W, h, w),
        result >= 0
// </vc-spec>
// <vc-code>
{
    assume(false);
    0int
}
// </vc-code>


}

fn main() {}