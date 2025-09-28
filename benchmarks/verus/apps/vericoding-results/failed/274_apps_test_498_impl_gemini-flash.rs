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
/* helper modified by LLM (iteration 5): no helpers needed */

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
/* code modified by LLM (iteration 5): fixed integer type issues and added 'as int' casts */
{
    let n_int = n as int;
    let m_int = m as int;
    let k_int = k as int;

    let desk_idx_in_row_int = (k_int - 1) % (2 * m_int);
    let desk_int = desk_idx_in_row_int / 2 + 1;
    let side_char = if desk_idx_in_row_int % 2 == 0 { 'L' } else { 'R' };
    let lane_int = (k_int - 1) / (2 * m_int) + 1;

    (lane_int as i32, desk_int as i32, side_char)
}
// </vc-code>


}

fn main() {}