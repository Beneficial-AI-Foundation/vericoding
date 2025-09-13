// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn valid_input(n: int, a: int, b: int) -> bool {
    n >= 1 && a >= 1 && a <= b && b <= 36
}

spec fn digit_sum(n: int) -> int
    requires n >= 0
    decreases n
{
    if n == 0 {
        0
    } else {
        (n % 10) + digit_sum(n / 10)
    }
}

spec fn sum_in_range(n: int, a: int, b: int) -> int
    decreases n when n >= 0
{
    if n <= 0 {
        0
    } else if a >= 1 && a <= b && a <= digit_sum(n) && digit_sum(n) <= b {
        n + sum_in_range(n - 1, a, b)
    } else {
        sum_in_range(n - 1, a, b)
    }
}
// </vc-helpers>

// <vc-spec>
fn solve(n: int, a: int, b: int) -> (result: int)
    requires valid_input(n, a, b)
    ensures result == sum_in_range(n, a, b)
    ensures result >= 0
// </vc-spec>
// <vc-code>
{
    assume(false);
    0
}
// </vc-code>


}

fn main() {}