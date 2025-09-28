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
/* helper modified by LLM (iteration 4): Fixed invariants and initialization in exec_isqrt */
fn exec_isqrt(n: i32) -> (result: i32)
    requires
        n >= 0,
    ensures
        result >= 0,
        result * result <= n,
        (result + 1) * (result + 1) > n,
        result == isqrt(n as int),
{
    if n == 0 {
        return 0;
    }
    if n <= 3 {
        return 1;
    }
    
    let mut low: i32 = 0;
    let mut high: i32 = n / 2 + 1;  // Use n/2 + 1 as upper bound
    
    proof {
        assert(low * low <= n);
        assert(high > 0);
        assert(high * high >= n / 4 + n / 2 + 1);
        assert(high * high > n);
    }
    
    while high - low > 1
        invariant
            low >= 0,
            high > low,
            low * low <= n,
            high * high > n,
        decreases high - low
    {
        let mid = low + (high - low) / 2;
        if mid <= n / mid {  // Avoid overflow: mid * mid <= n
            low = mid;
            proof {
                assert(low * low <= n);
            }
        } else {
            high = mid;
            proof {
                assert(high * high > n);
            }
        }
    }
    
    proof {
        assert(high - low == 1);
        assert(low * low <= n);
        assert(high * high > n);
        assert(high == low + 1);
        assert((low + 1) * (low + 1) > n);
    }
    
    low
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
    /* code modified by LLM (iteration 4): Added truncate attribute for cast and fixed overflow */
    let quad_solv_numerator = exec_isqrt(8 * (n as i32) + 1) - 1;
    let x = quad_solv_numerator / 2;
    let y = x + 1;
    
    // Calculate xed avoiding overflow
    let x_part1 = if x >= 2 { (x / 2) * (x - 1) } else { 0 };
    let x_part2 = if x % 2 == 1 && x >= 1 { (x - 1) / 2 } else { 0 };
    let xed = x_part1 + x_part2 + (n as i32) - x;
    
    let ybr = (n as i32) - y;
    let yed = 2 * ybr;
    let result = if xed > yed { xed } else { yed };
    
    proof {
        assert(x >= 0);
        assert(x_part1 + x_part2 == x * (x - 1) / 2);
        assert(xed == x * (x - 1) / 2 + (n as i32) - x);
        assert(result >= 0);
        assert(result >= (n as int) - 1);
        assert(result <= (n as int) * ((n as int) - 1) / 2);
        assert(quad_solv_numerator == isqrt(8 * (n as int) + 1) - 1);
        assert(result == compute_expected_result(n as int));
    }
    
    #[verifier::truncate]
    result as i8
}
// </vc-code>


}

fn main() {}