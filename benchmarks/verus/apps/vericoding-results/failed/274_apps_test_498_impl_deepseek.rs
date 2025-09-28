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

proof fn lemma_div_mod_relation(a: int, b: int)
    requires
        b > 0,
    ensures
        a == b * (a / b) + a % b,
        a % b >= 0,
        a % b < b,
{
    /* helper modified by LLM (iteration 5): Using vstd arithmetic division lemma */
    vstd::arithmetic::div_mod::div_mod_auto(a, b);
}

proof fn lemma_div_mod_properties(n: int, m: int, k: int)
    requires
        n >= 1,
        m >= 1,
        k >= 1,
        k <= 2 * n * m,
    ensures
        (k - 1) / (2 * m) >= 0,
        (k - 1) / (2 * m) < n,
        (k - 1) % (2 * m) >= 0,
        (k - 1) % (2 * m) < 2 * m,
{
    /* helper modified by LLM (iteration 5): Updated to use div_mod_auto lemma */
    lemma_div_mod_relation(k - 1, 2 * m);
    
    let div_result = (k - 1) / (2 * m);
    assert(div_result >= 0) by {
        assert(k >= 1);
        assert(k - 1 >= 0);
        assert(2 * m >= 2);
    };
    assert(div_result < n) by {
        assert(k <= 2 * n * m);
        assert(k - 1 < 2 * n * m);
        assert((2 * m) * n == 2 * n * m);
    };
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
    /* code modified by LLM (iteration 5): Using fixed lemma with correct vstd function */
    proof {
        lemma_div_mod_properties(n as int, m as int, k as int);
        assert((k as int - 1) / (2 * (m as int)) < n as int);
    }
    
    let k_minus_one = (k - 1) as i32;
    let lane = k_minus_one / (2 * m) + 1;
    let remainder = k_minus_one % (2 * m);
    let desk = remainder / 2 + 1;
    let side = if remainder % 2 == 0 { 'L' } else { 'R' };
    
    (lane, desk, side)
}
// </vc-code>


}

fn main() {}