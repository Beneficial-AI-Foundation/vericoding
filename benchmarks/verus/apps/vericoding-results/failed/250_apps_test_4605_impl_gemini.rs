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
/* helper modified by LLM (iteration 5): fix syntax of assert-by block for proving digit_sum bound */
fn compute_digit_sum(n_orig: i8) -> (ds: i8)
    requires n_orig >= 0
    ensures ds >= 0, ds as int == digit_sum(n_orig as int)
{
    let mut n = n_orig as i32;
    let mut sum: i32 = 0;

    while n > 0
        invariant
            n >= 0,
            n_orig as int >= 0,
            sum >= 0,
            digit_sum(n_orig as int) == sum + digit_sum(n as int),
        decreases n
    {
        let rem = n % 10;
        sum = sum + rem;
        n = n / 10;
    }

    assert(sum == digit_sum(n_orig as int));
    assert(digit_sum(n_orig as int) <= 18) by {
        assert_by_compute(forall|i: int| 0 <= i && i <= 127 ==> digit_sum(i) <= 18);
    }

    sum as i8
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
/* code modified by LLM (iteration 5): kept previous logic, should be correct after helper fix */
{
    let mut total: i32 = 0;
    let mut i: i32 = 1;
    let n_i32 = n as i32;
    while i <= n_i32
        invariant
            1 <= i <= n_i32 + 1,
            n_i32 == n as i32,
            total >= 0,
            total as int <= ((i - 1) * i) / 2,
            total as int == sum_in_range((i - 1) as int, a as int, b as int),
            valid_input(n as int, a as int, b as int),
        decreases n_i32 - i
    {
        let ds = compute_digit_sum(i as i8);
        if a <= ds && ds <= b {
            total = total + i;
        }
        i = i + 1;
    }
    total as i8
}

// </vc-code>


}

fn main() {}