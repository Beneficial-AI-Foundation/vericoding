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
/* helper modified by LLM (iteration 5): compute solution spec */
spec fn compute_solution(n: int, m: int, k: int) -> (int, int, char)
    requires valid_input(n, m, k)
    ensures correct_solution(n, m, k, result.0, result.1, result.2)
{
    let t = k - 1;
    let denom = 2 * m;
    let lane = t / denom + 1;
    let rem = t % denom;
    let desk = rem / 2 + 1;
    let side = if rem % 2 == 0 { 'L' } else { 'R' };
    (lane, desk, side)
}
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
{
    /* code modified by LLM (iteration 5): compute with i32 and return named result for ensures */
    let t: i32 = k - 1;
    let denom: i32 = 2 * m;
    let lane: i32 = t / denom + 1;
    let rem: i32 = t % denom;
    let desk: i32 = rem / 2 + 1;
    let side: char = if rem % 2 == 0 { 'L' } else { 'R' };
    let result: (i32, i32, char) = (lane, desk, side);
    proof {
        let n_i: int = n as int;
        let m_i: int = m as int;
        let k_i: int = k as int;
        let lane_i: int = lane as int;
        let desk_i: int = desk as int;
        let side_i: char = side;
        assert(1 <= lane_i && lane_i <= n_i);
        assert(1 <= desk_i && desk_i <= m_i);
        assert(side_i == 'L' || side_i == 'R');
        assert(lane_i == (k_i - 1) / (2 * m_i) + 1);
        assert(desk_i == (k_i - 1) % (2 * m_i) / 2 + 1);
        assert((side_i == 'L') <==> ((k_i - 1) % (2 * m_i) % 2 == 0));
    }
    result
}
// </vc-code>


}

fn main() {}