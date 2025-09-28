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
/* helper modified by LLM (iteration 2): executable digit sum over i32 linked to spec digit_sum */
fn exec_digit_sum32(x: i32) -> (res: i32)
    requires
        x >= 0,
    ensures
        res as int == digit_sum(x as int),
        res >= 0,
{
    let mut m: i32 = x;
    let mut s: i32 = 0;
    while m > 0
        invariant
            m >= 0,
            s >= 0,
            (s as int) + digit_sum(m as int) == digit_sum(x as int),
        decreases m
    {
        s = s + (m % 10);
        m = m / 10;
    }
    s
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
    /* code modified by LLM (iteration 2): use machine ints with ghost reasoning; remove exec int vars */
    let ni: i32 = n as i32;
    let ai: i32 = a as i32;
    let bi: i32 = b as i32;

    let mut i: i32 = 1;
    let mut acc: i32 = 0;

    while i <= ni
        invariant
            1 <= i && i <= ni + 1,
            (acc as int) == sum_in_range((i as int) - 1, a as int, b as int),
            acc >= 0,
        decreases (ni as int) - (i as int) + 1
    {
        let ds: i32 = exec_digit_sum32(i);
        if ai <= ds && ds <= bi {
            acc = acc + i;
            proof {
                assert(ds as int == digit_sum(i as int));
                assert(a as int <= digit_sum(i as int) && digit_sum(i as int) <= b as int);
                assert(sum_in_range(i as int, a as int, b as int) == (i as int) + sum_in_range(i as int - 1, a as int, b as int));
            }
        } else {
            proof {
                assert(ds as int == digit_sum(i as int));
                assert(!(a as int <= digit_sum(i as int) && digit_sum(i as int) <= b as int));
                assert(sum_in_range(i as int, a as int, b as int) == sum_in_range(i as int - 1, a as int, b as int));
            }
        }
        i = i + 1;
    }

    let result: i8 = acc as i8;
    result
}
// </vc-code>


}

fn main() {}