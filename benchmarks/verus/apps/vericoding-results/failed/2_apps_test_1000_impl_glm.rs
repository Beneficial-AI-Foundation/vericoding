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

// </vc-helpers>

// <vc-spec>
fn solve(n: i8, v: i8) -> (result: i8)
    requires valid_input(n as int, v as int)
    ensures result as int == min_cost(n as int, v as int)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 3): using i32 for intermediate computation to avoid overflow */
{
    let n_i32 = n as i32;
    let v_i32 = v as i32;
    let req = n_i32 - 1;
    let result_i32 = if req <= v_i32 {
        req
    } else {
        let remaining = req - v_i32;
        v_i32 + remaining * (remaining + 3) / 2
    };
    let result = result_i32 as i8;
    result
}
// </vc-code>


}

fn main() {}