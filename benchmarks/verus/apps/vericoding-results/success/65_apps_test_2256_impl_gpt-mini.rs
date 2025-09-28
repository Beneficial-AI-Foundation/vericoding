// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(n: int, x: int, a: int, b: int) -> bool {
    2 <= n <= 100 && 0 <= x <= 100 && 1 <= a <= n && 1 <= b <= n && a != b
}

spec fn max_distance(n: int, x: int, a: int, b: int) -> int
    recommends valid_input(n, x, a, b)
{
    let initial_distance = if a >= b { a - b } else { b - a };
    let max_possible_distance = initial_distance + x;
    let max_line_distance = n - 1;
    if max_possible_distance <= max_line_distance { max_possible_distance } else { max_line_distance }
}

spec fn valid_result(n: int, x: int, a: int, b: int, result: int) -> bool
    recommends valid_input(n, x, a, b)
{
    result == max_distance(n, x, a, b) && 0 <= result <= n - 1
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): prove abs difference <= n-1 */
proof fn abs_diff_le(n: int, a: int, b: int)
    requires
        1 <= a <= n,
        1 <= b <= n,
    ensures
        if a >= b { a - b <= n - 1 } else { b - a <= n - 1 },
{
    if a >= b {
        assert(a - b <= n - 1);
    } else {
        assert(b - a <= n - 1);
    }
}

// </vc-helpers>

// <vc-spec>
fn solve_rival_distance(n: i8, x: i8, a: i8, b: i8) -> (result: i8)
    requires
        valid_input(n as int, x as int, a as int, b as int),
    ensures
        valid_result(n as int, x as int, a as int, b as int, result as int),
        result >= 0,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 4): compute max distance using i8 arithmetic and prove with ghost ints */
    let initial_distance_i8: i8 = if a >= b { a - b } else { b - a };
    let max_line_i8: i8 = n - 1;
    let diff_space: i8 = max_line_i8 - initial_distance_i8;
    let res_i8: i8 = if x <= diff_space { initial_distance_i8 + x } else { max_line_i8 };

    proof {
        let ni: int = n as int;
        let xi: int = x as int;
        let ai: int = a as int;
        let bi: int = b as int;

        assert(2 <= ni <= 100);
        assert(0 <= xi <= 100);
        assert(1 <= ai <= ni);
        assert(1 <= bi <= ni);

        abs_diff_le(ni, ai, bi);

        let initial_distance: int = if ai >= bi { ai - bi } else { bi - ai };
        let max_line_distance: int = ni - 1;

        assert(initial_distance == (initial_distance_i8 as int));
        assert(max_line_distance == (max_line_i8 as int));

        if xi <= max_line_distance - initial_distance {
            assert(res_i8 as int == initial_distance + xi);
        } else {
            assert(res_i8 as int == max_line_distance);
        }

        assert(0 <= (res_i8 as int) && (res_i8 as int) <= ni - 1);
    }

    res_i8
}

// </vc-code>


}

fn main() {}