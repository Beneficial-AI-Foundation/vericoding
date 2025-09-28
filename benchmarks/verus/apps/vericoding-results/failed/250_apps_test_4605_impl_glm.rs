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
/* helper modified by LLM (iteration 3): use u8 for internal variables to avoid arithmetic issues */
fn compute_digit_sum(x: i8) -> (sum: i8)
    requires x >= 0
    ensures sum as int == digit_sum(x as int)
{
    let mut total: u8 = 0;
    let mut current: u8 = x as u8;
    while current > 0
        invariant
            total as int + digit_sum(current as int) == digit_sum(x as int)
        decreases current
    {
        total += current % 10;
        current /= 10;
    }
    total as i8
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
/* code modified by LLM (iteration 3): use u8 for loop counter and i32 for sum to avoid overflow */
{
    let mut total: i32 = 0;
    let mut i: u8 = 1;
    while i <= n as u8
        invariant
            1 <= i && i <= (n as u8)+1,
            total as int == sum_in_range((i-1) as int, a as int, b as int)
        decreases (n as u8) - i
    {
        let ds = compute_digit_sum(i as i8) as i32;
        if a as i32 <= ds && ds <= b as i32 {
            total += i as i32;
        }
        i += 1;
    }
    total as i8
}
// </vc-code>


}

fn main() {}