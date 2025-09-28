// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(n: int, m: int, k: int) -> bool {
    1 <= n <= 10000 && 1 <= m <= 10000 && 1 <= k <= 2 * n * m
}

spec fn valid_output(n: int, m: int, lane: int, desk: int, side: char) -> bool {
    1 <= lane <= n && 1 <= desk <= m && (side == 'L' || side == 'R')
}

spec fn correct_solution(n: int, m: int, k: int, lane: int, desk: int, side: char) -> bool
    recommends valid_input(n, m, k)
{
    lane == (k - 1) / (2 * m) + 1 &&
    desk == (k - 1) % (2 * m) / 2 + 1 &&
    (side == 'L' <==> (k - 1) % (2 * m) % 2 == 0)
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn solve(n: i32, m: i32, k: i32) -> (result: (i32, i32, char))
    requires valid_input(n as int, m as int, k as int)
    ensures ({
        let (lane, desk, side) = result;
        valid_output(n as int, m as int, lane as int, desk as int, side) &&
        correct_solution(n as int, m as int, k as int, lane as int, desk as int, side)
    })
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Compute in int to match spec exactly, then cast to i32 for output */
{
    let pos = k as int - 1;
    let per_lane = 2 * m as int;
    let lane = pos / per_lane + 1;
    let within = pos % per_lane;
    let desk = within / 2 + 1;
    let is_left = within % 2 == 0;
    let side = if is_left { 'L' } else { 'R' };
    proof {
        assert(correct_solution(n as int, m as int, k as int, lane, desk, side));
    }
    (lane as i32, desk as i32, side)
}
// </vc-code>


}

fn main() {}