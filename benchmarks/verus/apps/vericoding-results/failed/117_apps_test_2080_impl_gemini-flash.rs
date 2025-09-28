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
/* helper modified by LLM (iteration 4): removed. */
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
/* code modified by LLM (iteration 4): corrected type conversions from `i8` to `int` and back, ensuring calculations use Verus `int` for verification and correct `i8` conversion at the end. */
{
    let n_int = n as int;
    let quad_solv_numerator = isqrt(8 * n_int + 1) - 1;
    let x: int = quad_solv_numerator / 2;
    let y: int = x + 1;
    let xed: int = x * (x - 1) / 2 + n_int - x;
    let ybr: int = n_int - y;
    let yed: int = 2 * ybr;

    let final_result_int: int;
    if xed > yed {
        final_result_int = xed;
    } else {
        final_result_int = yed;
    }

    final_result_int as i8
}
// </vc-code>


}

fn main() {}