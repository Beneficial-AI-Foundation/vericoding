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
/* helper modified by LLM (iteration 5): fixed overflow arithmetic and established proper invariants */
fn isqrt_exec(n: i32) -> (result: i32)
    requires
        n >= 0,
    ensures
        result >= 0,
        result * result <= n,
        (result + 1) * (result + 1) > n,
{
    if n <= 1 {
        n
    } else {
        let mut low = 0i32;
        let mut high = if n <= 46340 * 46340 { 
            let temp = n + 1;
            if temp <= 46341 { temp } else { 46341 }
        } else { 
            46341 
        };
        
        proof {
            if n <= 46340 * 46340 {
                let temp = n + 1;
                if temp <= 46341 {
                    assert(temp * temp > n);
                } else {
                    assert(46341 * 46341 > n);
                }
            } else {
                assert(46341 * 46341 > n);
            }
        }
        
        while high - low > 1
            invariant
                0 <= low < high,
                low * low <= n,
                high * high > n,
                high <= 46341,
            decreases high - low
        {
            let mid = low + (high - low) / 2;
            proof {
                assert(mid < high);
                assert(mid <= 46340);
            }
            let mid_squared = mid * mid;
            if mid_squared <= n {
                low = mid;
            } else {
                high = mid;
            }
        }
        
        proof {
            assert(low * low <= n);
            assert((low + 1) * (low + 1) > n);
        }
        
        low
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
/* code modified by LLM (iteration 5): fixed arithmetic overflow and bounds checking */
{
    let n32 = n as i32;
    let sqrt_val = isqrt_exec(8 * n32 + 1);
    let quad_solv_numerator = sqrt_val - 1;
    let x = quad_solv_numerator / 2;
    let y = x + 1;
    
    proof {
        assert(n32 >= 1 && n32 <= 127);
        assert(x >= 0);
        assert(8 * n32 + 1 <= 1017);
        assert(sqrt_val <= 32);
        assert(x <= 15);
    }
    
    let xed = if x > 0 { 
        let temp1 = x * (x - 1);
        let temp2 = temp1 / 2;
        temp2 + n32 - x
    } else { 
        n32
    };
    let ybr = n32 - y;
    let yed = if ybr >= 0 { 2 * ybr } else { 0 };
    
    proof {
        assert(xed >= 0);
        assert(yed >= 0);
        assert(xed <= 127);
        assert(yed <= 127);
    }
    
    if xed > yed {
        xed as i8
    } else {
        yed as i8
    }
}
// </vc-code>


}

fn main() {}