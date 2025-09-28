// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn valid_input(n: int) -> bool {
    1 <= n <= 2000000000
}

spec fn valid_output(n: int, result: int) -> bool {
    result >= 0 &&
    result >= n - 1 &&
    result <= n * (n - 1) / 2
}

spec fn compute_expected_result(n: int) -> int {
    let quad_solv_numerator = isqrt(8*n + 1) - 1;
    let x = quad_solv_numerator / 2;
    let y = x + 1;
    let xed = x * (x - 1) / 2 + n - x;
    let ybr = n - y;
    let yed = 2 * ybr;
    if xed > yed { xed } else { yed }
}

spec fn isqrt(n: int) -> int {
    if n == 0 { 0 }
    else if n == 1 { 1 }
    else if n <= 3 { 1 }
    else {
        let guess = n / 2;
        let low = 0;
        let high = guess + 1;
        isqrt_helper(n, low, high)
    }
}

spec fn isqrt_helper(n: int, low: int, high: int) -> int
    decreases high - low
{
    if high - low <= 1 { low }
    else {
        let mid = (low + high) / 2;
        if mid * mid <= n {
            isqrt_helper(n, mid, high)
        } else {
            isqrt_helper(n, low, mid)
        }
    }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): executable isqrt helper */
fn isqrt_exec_helper(n: int, low: int, high: int) -> int
    requires
        0 <= n, low <= high,
    decreases
        high - low,
    ensures
        result == isqrt_helper(n, low, high),
{
    if high - low <= 1 {
        low
    } else {
        let mid = (low + high) / 2;
        if mid * mid <= n {
            isqrt_exec_helper(n, mid, high)
        } else {
            isqrt_exec_helper(n, low, mid)
        }
    }
}

/* helper modified by LLM (iteration 5): top-level isqrt exec */
fn isqrt_exec(n: int) -> int
    requires
        0 <= n,
    ensures
        result == isqrt(n),
{
    if n == 0 { 0 }
    else if n == 1 { 1 }
    else if n <= 3 { 1 }
    else {
        let guess = n / 2;
        let low = 0;
        let high = guess + 1;
        isqrt_exec_helper(n, low, high)
    }
}

// </vc-helpers>

// <vc-spec>
fn solve(n: i8) -> (result: i8)
    requires 
        valid_input(n as int),
    ensures
        valid_output(n as int, result as int),
        result as int == compute_expected_result(n as int),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): compute expected result using isqrt_exec and return as i8 */
    let ni = n as int;
    let s = isqrt_exec(8 * ni + 1);
    let quad_solv_numerator = s - 1;
    let x = quad_solv_numerator / 2;
    let y = x + 1;
    let xed = x * (x - 1) / 2 + ni - x;
    let ybr = ni - y;
    let yed = 2 * ybr;
    let res_int = if xed > yed { xed } else { yed };
    proof {
        assert(isqrt(8 * ni + 1) == s);
        assert(res_int == compute_expected_result(ni));
    }
    res_int as i8
}

// </vc-code>


}

fn main() {}