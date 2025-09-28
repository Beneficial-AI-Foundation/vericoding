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
/* helper modified by LLM (iteration 5): fixed division lemmas with proper arithmetic proofs */
proof fn lemma_division_basic(a: int, b: int)
    requires b > 0
    ensures a / b * b <= a
{
    assert(a == (a / b) * b + (a % b));
    assert(a % b >= 0);
}

proof fn lemma_division_upper_bound(a: int, b: int, c: int)
    requires b > 0, a <= c
    ensures a / b <= c / b
{
    assert(a / b * b <= a) by { lemma_division_basic(a, b); };
    assert(c / b * b <= c) by { lemma_division_basic(c, b); };
}

proof fn lemma_division_properties(n: int, m: int, k: int)
    requires valid_input(n, m, k)
    ensures
        0 <= (k - 1) / (2 * m) < n,
        0 <= (k - 1) % (2 * m) / 2 < m,
        (k - 1) % (2 * m) % 2 == 0 || (k - 1) % (2 * m) % 2 == 1
{
    lemma_division_basic(k - 1, 2 * m);
    assert(k >= 1);
    assert(2 * m >= 2);
    assert(k - 1 >= 0);
    assert(k <= 2 * n * m);
    assert(k - 1 < 2 * n * m);
    assert(2 * n * m == n * (2 * m));
    assert((k - 1) / (2 * m) < n) by {
        lemma_division_upper_bound(k - 1, 2 * m, 2 * n * m - 1);
        assert((2 * n * m - 1) / (2 * m) == n - 1);
    };
    assert((k - 1) % (2 * m) < 2 * m);
    assert((k - 1) % (2 * m) / 2 < m);
}

proof fn lemma_correct_calculation(n: int, m: int, k: int)
    requires valid_input(n, m, k)
    ensures
        valid_output(n, m, (k - 1) / (2 * m) + 1, (k - 1) % (2 * m) / 2 + 1, if (k - 1) % (2 * m) % 2 == 0 { 'L' } else { 'R' }),
        correct_solution(n, m, k, (k - 1) / (2 * m) + 1, (k - 1) % (2 * m) / 2 + 1, if (k - 1) % (2 * m) % 2 == 0 { 'L' } else { 'R' })
{
    lemma_division_properties(n, m, k);
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
    /* code modified by LLM (iteration 5): no changes needed in code body */
    proof {
        lemma_correct_calculation(n as int, m as int, k as int);
    }
    
    let lane = (k - 1) / (2 * m) + 1;
    let desk = (k - 1) % (2 * m) / 2 + 1;
    let side = if (k - 1) % (2 * m) % 2 == 0 { 'L' } else { 'R' };
    
    (lane, desk, side)
}
// </vc-code>


}

fn main() {}