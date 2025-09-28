// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(n: int, k: int) -> bool {
    2 <= n <= 5000 && 1 <= k <= n
}

spec fn optimal_moves(n: int, k: int) -> int {
    if k == 1 || k == n {
        3 * n
    } else {
        3 * n + spec_min(k - 1, n - k)
    }
}

spec fn spec_min(a: int, b: int) -> int {
    if a <= b { a } else { b }
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn minimum_moves(n: i8, k: i8) -> (result: i8)
    requires 
        valid_input(n as int, k as int)
    ensures 
        result as int == optimal_moves(n as int, k as int),
        result > 0
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): Used executable i32 types instead of spec int to fix compilation errors */
    let nn = n as i32;
    let kk = k as i32;
    let result_int: i32;
    if kk == 1 || kk == nn {
        result_int = 3 * nn;
    } else {
        let diff1 = kk - 1;
        let diff2 = nn - kk;
        let min_val = if diff1 <= diff2 { diff1 } else { diff2 };
        result_int = 3 * nn + min_val;
    }
    result_int as i8
}
// </vc-code>


}

fn main() {}