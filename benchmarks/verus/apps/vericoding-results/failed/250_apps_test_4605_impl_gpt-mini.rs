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
/* helper modified by LLM (iteration 5): executable digit sum implementation using i64 */
fn compute_digit_sum_impl(mut m: i64) -> i64 {
    let mut res: i64 = 0;
    while m > 0
        invariant
            m >= 0,
            res >= 0,
        decreases
            m
    {
        let d = m % 10;
        res = res + d;
        m = m / 10;
    }
    res
}

/* helper modified by LLM (iteration 5): proof linking implementation to spec digit_sum */
fn compute_digit_sum_correct(n: i64) -> ()
    requires
        n >= 0,
    ensures
        (compute_digit_sum_impl(n) as int) == digit_sum(n as int),
    decreases
        n
{
    let mut m = n;
    let mut acc: i64 = 0;
    while m > 0
        invariant
            m >= 0,
            (acc as int) + digit_sum(m as int) == digit_sum(n as int),
        decreases
            m
    {
        let d = m % 10;
        acc = acc + d;
        m = m / 10;
    }
    ()
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
    /* code modified by LLM (iteration 5): iterative sum using compute_digit_sum_impl */
    let N: i64 = n as i64;
    let a_i: i64 = a as i64;
    let b_i: i64 = b as i64;
    let mut i: i64 = 1;
    let mut acc: i64 = 0;
    while i <= N
        invariant
            1 <= i && i <= N + 1,
            (acc as int) == sum_in_range((i - 1) as int, a as int, b as int),
        decreases
            N - i + 1
    {
        let ds = compute_digit_sum_impl(i);
        proof {
            compute_digit_sum_correct(i);
            assert((ds as int) == digit_sum(i as int));
        }
        if a_i <= ds && ds <= b_i {
            acc = acc + i;
        }
        i = i + 1;
    }
    let result = acc as i8;
    result
}
// </vc-code>


}

fn main() {}