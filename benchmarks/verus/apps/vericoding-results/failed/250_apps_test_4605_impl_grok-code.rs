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
/* helper modified by LLM (iteration 2): adjusted exec_digit_sum to use usize for executable computation */
fn exec_digit_sum(n: usize) -> (res: usize)
    requires n >= 0
    ensures res == digit_sum(n as int)
    decreases n
{
    if n == 0 {
        0
    } else {
        (n % 10) + exec_digit_sum(n / 10)
    }
}

/* helper modified by LLM (iteration 2): adjusted exec_sum_in_range to use usize for executable computation */
fn exec_sum_in_range(n: usize, a: usize, b: usize) -> (res: usize)
    requires n >= 0 && a >= 1 && a <= b && b <= 36
    ensures res == sum_in_range(n as int, a as int, b as int)
    decreases n
{
    if n == 0 {
        0
    } else {
        let ds = exec_digit_sum(n);
        if a <= ds && ds <= b {
            n + exec_sum_in_range(n - 1, a, b)
        } else {
            exec_sum_in_range(n - 1, a, b)
        }
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
    /* code modified by LLM (iteration 2): call exec_sum_in_range with usize casts */
    let result = exec_sum_in_range(n as usize, a as usize, b as usize);
    result as i8
}
// </vc-code>


}

fn main() {}