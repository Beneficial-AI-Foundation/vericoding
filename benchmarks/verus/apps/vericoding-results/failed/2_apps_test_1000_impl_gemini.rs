// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(n: int, v: int) -> bool {
    2 <= n <= 100 && 1 <= v <= 100
}

spec fn min_cost(n: int, v: int) -> int {
    let req = n - 1;
    if req <= v {
        req
    } else {
        let remaining = req - v;
        v + remaining * (remaining + 3) / 2
    }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): [lemma to prove product is always even] */
proof fn lemma_even_product(x: int)
    ensures (x * (x + 3)) % 2 == 0
{
    if x % 2 == 0 {
    } else {
        assert((x + 3) % 2 == 0);
    }
}
// </vc-helpers>

// <vc-spec>
fn solve(n: i8, v: i8) -> (result: i8)
    requires valid_input(n as int, v as int)
    ensures result as int == min_cost(n as int, v as int)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): [use i64 for calculation and add lemma call] */
    let n_calc = n as i64;
    let v_calc = v as i64;
    let req = n_calc - 1;

    if req <= v_calc {
        req as i8
    } else {
        let remaining = req - v_calc;
        lemma_even_product(remaining as int);
        let cost = v_calc + remaining * (remaining + 3) / 2;
        cost as i8
    }
}
// </vc-code>


}

fn main() {}