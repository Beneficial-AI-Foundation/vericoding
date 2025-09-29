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
/* helper modified by LLM (iteration 2): nonnegativity of absolute difference */
pub proof fn abs_diff_nonnegative(a: int, b: int)
    ensures
        0 <= if a >= b { a - b } else { b - a },
{
    if a >= b {
        assert(a - b >= 0);
    } else {
        assert(b - a >= 0);
    }
}

/* helper modified by LLM (iteration 2): bounds on n-1 within i8 range */
pub proof fn lemma_n_minus_one_bounds(n: int)
    requires
        2 <= n,
        n <= 100,
    ensures
        0 <= n - 1,
        n - 1 <= 127,
{
    assert(n - 1 <= 99);
    assert(99 <= 127);
}

/* helper modified by LLM (iteration 2): relate b <= c - a and a + b <= c */
pub proof fn lemma_le_sub_iff_add_le(a: int, b: int, c: int)
    ensures
        b <= c - a ==> a + b <= c,
        a + b <= c ==> b <= c - a,
{
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
    /* code modified by LLM (iteration 2): overflow-safe i8 computation with proofs equating to the spec */
    let d: i8 = if a >= b { a - b } else { b - a };
    let n_minus_1: i8 = n - 1;

    // Establish d <= n-1 (as ints) to justify subtraction for cap
    proof {
        let ghost ni: int = n as int;
        let ghost xi: int = x as int;
        let ghost ai: int = a as int;
        let ghost bi: int = b as int;
        assert(valid_input(ni, xi, ai, bi));
        if a >= b {
            assert(d as int == ai - bi);
            assert(ai - bi <= ni - 1);
        } else {
            assert(d as int == bi - ai);
            assert(bi - ai <= ni - 1);
        }
        assert((d as int) <= (n_minus_1 as int));
    }

    let cap: i8 = n_minus_1 - d;

    let result: i8;
    if x <= cap {
        // Prove addition fits in i8
        proof {
            let ghost ni: int = n as int;
            let ghost xi: int = x as int;
            let ghost ai: int = a as int;
            let ghost bi: int = b as int;
            assert(valid_input(ni, xi, ai, bi));
            if a >= b {
                assert(d as int == ai - bi);
                assert(ai - bi <= ni - 1);
            } else {
                assert(d as int == bi - ai);
                assert(bi - ai <= ni - 1);
            }
            assert(xi <= (n_minus_1 as int) - (d as int));
            lemma_le_sub_iff_add_le(d as int, xi, n as int - 1);
            assert((d as int) + xi <= (n as int - 1));
        }
        result = d + x;
    } else {
        result = n_minus_1;
    }

    proof {
        let ghost ni: int = n as int;
        let ghost xi: int = x as int;
        let ghost ai: int = a as int;
        let ghost bi: int = b as int;
        assert(valid_input(ni, xi, ai, bi));

        let ghost initial_distance: int = if ai >= bi { ai - bi } else { bi - ai };
        let ghost max_line_distance: int = ni - 1;

        // Link d and initial_distance
        if a >= b {
            assert(d as int == ai - bi);
            assert(initial_distance == ai - bi);
        } else {
            assert(d as int == bi - ai);
            assert(initial_distance == bi - ai);
        }

        lemma_n_minus_one_bounds(ni);
        assert(n_minus_1 as int == max_line_distance);

        // cap integer relation and its range
        assert((d as int) <= max_line_distance);
        assert(0 <= max_line_distance - (d as int));
        assert(max_line_distance - (d as int) <= 127);
        assert(cap as int == max_line_distance - (d as int));

        lemma_le_sub_iff_add_le(d as int, xi, max_line_distance);

        if x <= cap {
            assert(xi <= max_line_distance - (d as int));
            assert((d as int) + xi <= max_line_distance);
            assert(((d + x) as int) == (d as int) + xi);
            assert(initial_distance + xi <= max_line_distance);
            assert(max_distance(ni, xi, ai, bi) == initial_distance + xi);
            assert(result as int == max_distance(ni, xi, ai, bi));
            assert(0 <= result as int);
            assert(result as int <= max_line_distance);
        } else {
            assert(xi > max_line_distance - (d as int));
            assert((d as int) + xi > max_line_distance);
            assert(max_distance(ni, xi, ai, bi) == max_line_distance);
            assert(result as int == max_distance(ni, xi, ai, bi));
            assert(0 <= result as int);
            assert(result as int <= max_line_distance);
        }
    }

    result
}
// </vc-code>


}

fn main() {}