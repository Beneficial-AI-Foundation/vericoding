// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(n: int, k: int, m: int, d: int) -> bool {
    2 <= n && 2 <= k <= n && 1 <= m <= n && 1 <= d <= n && m * d * k >= n
}

spec fn candies_used(x: int, d: int, k: int) -> int {
    x * ((d - 1) * k + 1)
}

spec fn valid_distribution(x: int, d: int, n: int, k: int, m: int, d_max: int) -> bool {
    1 <= x <= m && 1 <= d <= d_max && candies_used(x, d, k) <= n
}

spec fn person1_candies(x: int, d: int) -> int {
    x * d
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): multiplication monotonicity for nonnegative multiplier */
proof fn mul_le_mul_pos(a: int, b: int, c: int)
    requires
        c >= 0,
        a <= b,
    ensures
        a * c <= b * c,
{
    assert(a * c <= b * c);
}

// </vc-helpers>

// <vc-spec>
fn solve(n: i8, k: i8, m: i8, d: i8) -> (result: i8)
    requires valid_input(n as int, k as int, m as int, d as int)
    ensures
        result >= 0 &&
        result as int <= m as int * d as int &&
        (forall|x: int, d_val: int| valid_distribution(x, d_val, n as int, k as int, m as int, d as int) ==> person1_candies(x, d_val) <= result as int) &&
        (exists|x: int, d_val: int| valid_distribution(x, d_val, n as int, k as int, m as int, d as int) && person1_candies(x, d_val) == result as int)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): brute-force search over d and x ensuring correctness */
    let n_i: i64 = n as i64;
    let k_i: i64 = k as i64;
    let m_i: i64 = m as i64;
    let d_max_i: i64 = d as i64;

    let mut best: i64 = 0;
    let mut best_x: i64 = 0;
    let mut best_dv: i64 = 0;

    let mut d_val: i64 = 1;
    while d_val <= d_max_i
        invariant
            0 <= best,
            forall|x: int, dv: int| 1 <= dv && dv < d_val as int && valid_distribution(x, dv, n as int, k as int, m as int, d as int) ==> person1_candies(x, dv) <= best as int,
            (best == 0 || (1 <= best_x as int && best_x as int <= m as int && 1 <= best_dv as int && best_dv as int <= d as int && valid_distribution(best_x as int, best_dv as int, n as int, k as int, m as int, d as int) && person1_candies(best_x as int, best_dv as int) == best as int)),
        decreases
            d_max_i - d_val + 1
    {
        let mut x_val: i64 = 1;
        while x_val <= m_i
            invariant
                0 <= best,
                forall|x: int, dv: int| 1 <= dv && dv < d_val as int && valid_distribution(x, dv, n as int, k as int, m as int, d as int) ==> person1_candies(x, dv) <= best as int,
                (best == 0 || (1 <= best_x as int && best_x as int <= m as int && 1 <= best_dv as int && best_dv as int <= d as int && valid_distribution(best_x as int, best_dv as int, n as int, k as int, m as int, d as int) && person1_candies(best_x as int, best_dv as int) == best as int)),
            decreases
                m_i - x_val + 1
        {
            let used: i64 = x_val * ((d_val - 1) * k_i + 1);
            if used <= n_i {
                let candidate: i64 = x_val * d_val;
                if candidate > best {
                    best = candidate;
                    best_x = x_val;
                    best_dv = d_val;
                }
            }
            x_val = x_val + 1;
        }

        d_val = d_val + 1;
    }

    proof {
        // There is at least the (1,1) distribution, so best >= 1
        assert(1 <= m as int);
        assert(1 <= d as int);
        assert(candies_used(1, 1, k as int) <= n as int);
        assert(valid_distribution(1, 1, n as int, k as int, m as int, d as int));
        // after outer loop d_val == d_max_i + 1
        assert(1 < d_val as int);
        // from invariant forall for dv < d_val, dv=1 gives person1_candies(1,1) <= best
        assert(person1_candies(1, 1) <= best as int);
        assert(1 <= best as int);

        // since best != 0, we have witness stored
        assert(best != 0);
        assert(
            1 <= best_x as int && best_x as int <= m as int &&
            1 <= best_dv as int && best_dv as int <= d as int &&
            valid_distribution(best_x as int, best_dv as int, n as int, k as int, m as int, d as int) &&
            person1_candies(best_x as int, best_dv as int) == best as int
        );
        assert(best as int <= m as int * d as int);
    }

    (best as i8)
}
// </vc-code>


}

fn main() {}