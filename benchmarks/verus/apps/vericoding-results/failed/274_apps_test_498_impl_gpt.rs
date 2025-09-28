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
/* helper modified by LLM (iteration 4): prove bounds for lane and desk derived from k */
proof fn lemma_bounds(n: int, m: int, k: int)
    requires
        valid_input(n, m, k),
    ensures
        1 <= ((k - 1) / (2 * m) + 1) <= n,
        1 <= (((k - 1) % (2 * m)) / 2 + 1) <= m,
{
    let two_m = 2 * m;
    let x = k - 1;

    // From valid_input
    assert(1 <= n && 1 <= m && 1 <= k && 1 <= k && k <= 2 * n * m);

    // Basic positivity and bounds
    assert(two_m > 0);
    assert(0 <= x);

    // Show x < n * two_m using k <= 2*n*m and x = k - 1
    assert(x + 1 == k);
    assert(n * two_m == 2 * n * m);
    assert(x + 1 <= n * two_m);
    assert(x < n * two_m);

    // lane bounds
    assert(0 <= x / two_m);
    assert(x / two_m < n);
    assert(x / two_m <= n - 1);
    let lane = x / two_m + 1;
    assert(1 <= lane);
    assert(lane <= n);

    // desk bounds
    let r = x % two_m;
    assert(0 <= r && r < two_m);
    assert(0 <= r / 2);
    assert(r < 2 * m);
    assert(r / 2 < m);
    let desk = r / 2 + 1;
    assert(1 <= desk);
    assert(desk <= m);
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
    /* code modified by LLM (iteration 4): compute using int arithmetic, prove bounds, then cast safely to i32 */
    let n_i: int = n as int;
    let m_i: int = m as int;
    let k_i: int = k as int;

    let two_m_i: int = 2 * m_i;
    let x: int = k_i - 1;

    let lane_i: int = x / two_m_i + 1;
    let rem: int = x % two_m_i;
    let desk_i: int = rem / 2 + 1;
    let side_char: char = if rem % 2 == 0 { 'L' } else { 'R' };

    proof {
        // Prove bounds needed for valid_output and safe casts
        lemma_bounds(n_i, m_i, k_i);
        assert(1 <= n_i && n_i <= 10000);
        assert(1 <= m_i && m_i <= 10000);
        assert(1 <= lane_i && lane_i <= n_i);
        assert(1 <= desk_i && desk_i <= m_i);
        assert(lane_i <= 10000);
        assert(desk_i <= 10000);
        assert(-2147483648 <= lane_i && lane_i <= 2147483647);
        assert(-2147483648 <= desk_i && desk_i <= 2147483647);
        // Side relation matches the specification
        assert(side_char == 'L' <==> (rem % 2 == 0));
    }

    let lane32: i32 = lane_i as i32;
    let desk32: i32 = desk_i as i32;

    proof {
        // Round-trip casts for alignment with ensures which uses (lane as int)
        assert((lane32 as int) == lane_i);
        assert((desk32 as int) == desk_i);
        // Direct alignment with spec formulas
        assert(lane_i == (k_i - 1) / (2 * m_i) + 1);
        assert(desk_i == ((k_i - 1) % (2 * m_i)) / 2 + 1);
        assert((rem % 2) == (((k_i - 1) % (2 * m_i)) % 2));
    }

    (lane32, desk32, side_char)
}
// </vc-code>


}

fn main() {}