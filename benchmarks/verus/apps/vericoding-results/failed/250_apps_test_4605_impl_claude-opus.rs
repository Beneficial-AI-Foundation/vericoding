// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(n: int, a: int, b: int) -> bool {
    n >= 1 && a >= 1 && a <= b && b <= 36
}

spec fn digit_sum(n: int) -> int 
    decreases n
{
    if n <= 0 { 0 }
    else { (n % 10) + digit_sum(n / 10) }
}

spec fn sum_in_range(n: int, a: int, b: int) -> int
    decreases n
{
    if n <= 0 { 0 }
    else if a <= digit_sum(n) && digit_sum(n) <= b { 
        n + sum_in_range(n - 1, a, b) 
    }
    else { 
        sum_in_range(n - 1, a, b) 
    }
}
// </vc-preamble>

// <vc-helpers>
proof fn digit_sum_bounds(n: int)
    requires n >= 0
    ensures 0 <= digit_sum(n) <= 9 * (if n == 0 { 1 } else { n })
    decreases n
{
    if n <= 0 {
    } else {
        digit_sum_bounds(n / 10);
    }
}

proof fn sum_in_range_non_negative(n: int, a: int, b: int)
    requires
        n >= 0,
        a >= 1,
        b >= a
    ensures sum_in_range(n, a, b) >= 0
    decreases n
{
    if n <= 0 {
    } else {
        sum_in_range_non_negative(n - 1, a, b);
    }
}

/* helper modified by LLM (iteration 5): Simplified arithmetic assertions */
proof fn sum_in_range_bounded(n: int, a: int, b: int)
    requires
        0 <= n <= 127,
        a >= 1,
        b >= a
    ensures sum_in_range(n, a, b) <= n * (n + 1) / 2
    decreases n
{
    if n <= 0 {
    } else {
        sum_in_range_bounded(n - 1, a, b);
        if a <= digit_sum(n) && digit_sum(n) <= b {
            assert(sum_in_range(n, a, b) == n + sum_in_range(n - 1, a, b));
            assert(sum_in_range(n - 1, a, b) <= (n - 1) * n / 2);
            assert(n + (n - 1) * n / 2 <= n * (n + 1) / 2) by {
                assert(2 * n + (n - 1) * n == 2 * n + n * n - n);
                assert(2 * n + n * n - n == n * n + n);
                assert((n * n + n) / 2 == n * (n + 1) / 2);
            }
        } else {
            assert(sum_in_range(n, a, b) == sum_in_range(n - 1, a, b));
            assert(sum_in_range(n - 1, a, b) <= (n - 1) * n / 2);
            assert((n - 1) * n / 2 < n * (n + 1) / 2);
        }
    }
}

fn compute_digit_sum(n: i8) -> (result: i8)
    requires n >= 0
    ensures result as int == digit_sum(n as int)
    decreases n as int
{
    if n <= 0 {
        0
    } else {
        let d = n % 10;
        let rest = compute_digit_sum(n / 10);
        proof {
            digit_sum_bounds(n as int);
            assert(digit_sum(n as int) == (n % 10) as int + digit_sum((n / 10) as int));
            assert(0 <= d && d <= 9);
            digit_sum_bounds((n / 10) as int);
            assert(digit_sum((n / 10) as int) <= 9 * 12);
            assert(d as int + rest as int <= 9 + 9 * 12);
            assert(d as int + rest as int <= 117);
            assert(d as int + rest as int <= i8::MAX);
        }
        (d as i8) + rest
    }
}
// </vc-helpers>

// <vc-spec>
fn solve(n: i8, a: i8, b: i8) -> (result: i8)
    requires valid_input(n as int, a as int, b as int)
    ensures 
        result as int == sum_in_range(n as int, a as int, b as int) &&
        result >= 0
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Simplified arithmetic assertions in loop */
    let mut total: i8 = 0;
    let mut i: i8 = 1;
    
    proof {
        sum_in_range_bounded(n as int, a as int, b as int);
        assert(n <= 127);
        assert(n * (n + 1) / 2 <= 127 * 128 / 2) by {
            assert(127 * 128 == 16256);
            assert(16256 / 2 == 8128);
        }
        assert(sum_in_range(n as int, a as int, b as int) <= 8128);
    }
    
    while i <= n
        invariant
            1 <= i <= n + 1,
            a >= 1,
            a <= b,
            b <= 36,
            1 <= n <= 127,
            total as int == sum_in_range(i as int - 1, a as int, b as int),
            total >= 0,
            total as int <= (i - 1) * i / 2,
            (i - 1) * i / 2 <= 8128
        decreases (n as int) - (i as int) + 1
    {
        let ds = compute_digit_sum(i);
        proof {
            digit_sum_bounds(i as int);
            sum_in_range_non_negative(i as int - 1, a as int, b as int);
            sum_in_range_bounded(i as int - 1, a as int, b as int);
            assert(i <= n);
            assert(n <= 127);
            assert(i <= 127);
            assert(total as int <= (i - 1) * i / 2);
            
            assert((i - 1) * i / 2 + i <= i * (i + 1) / 2) by {
                assert(2 * ((i - 1) * i / 2 + i) == (i - 1) * i + 2 * i);
                assert((i - 1) * i + 2 * i == i * i - i + 2 * i);
                assert(i * i - i + 2 * i == i * i + i);
                assert(i * i + i == i * (i + 1));
            }
            
            assert(i * (i + 1) / 2 <= 127 * 128 / 2);
            assert(127 * 128 / 2 == 8128);
            
            if a <= digit_sum(i as int) && digit_sum(i as int) <= b as int {
                assert(total as int + i as int <= i * (i + 1) / 2);
                assert(i * (i + 1) / 2 <= 8128);
                assert(total as int + i as int <= 8128);
                assert(total as int + i as int <= i8::MAX);
            }
        }
        
        if a <= ds && ds <= b {
            total = total + i;
        }
        
        proof {
            if i == n {
                assert(i as int + 1 == n as int + 1);
                assert(n as int + 1 <= 128);
            } else {
                assert(i < n);
                assert(i <= 126);
            }
            assert(i as int + 1 <= 128);
            assert(i as int + 1 <= i8::MAX);
        }
        i = i + 1;
    }
    
    proof {
        sum_in_range_non_negative(n as int, a as int, b as int);
    }
    
    total
}
// </vc-code>


}

fn main() {}