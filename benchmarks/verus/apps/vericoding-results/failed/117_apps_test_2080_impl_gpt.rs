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
proof fn lemma_valid_input_bounds(n: int)
    requires
        valid_input(n),
    ensures
        1 <= n,
{
}

pub open spec fn max_int(a: int, b: int) -> int {
    if a > b { a } else { b }
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
    let x: i32 = n as i32;
    // compute s = isqrt(8*x + 1) as i32 via binary search
    let target: i32 = 8i32 * x + 1i32;
    let mut low: i32 = 0i32;
    let mut high: i32 = ((target) / 2i32) + 2i32;
    while high - low > 1i32
        invariant
            0i32 <= low,
            low < high,
        decreases (high - low) as int
    {
        let mid: i32 = (low + high) / 2i32;
        if mid * mid <= target {
            low = mid;
        } else {
            high = mid;
        }
    }
    let s: i32 = low; // s = isqrt(8*x + 1)
    let quad: i32 = s - 1i32;
    let xv: i32 = quad / 2i32;
    let y: i32 = xv + 1i32;
    let xed: i32 = (xv * (xv - 1i32)) / 2i32 + x - xv;
    let ybr: i32 = x - y;
    let yed: i32 = 2i32 * ybr;
    let t: i32 = if xed > yed { xed } else { yed };
    t as i8
}
// </vc-code>


}

fn main() {}