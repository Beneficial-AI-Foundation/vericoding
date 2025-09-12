// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn is_power_of_two(n: int) -> bool
    decreases n
{
    if n <= 0 {
        false
    } else if n == 1 {
        true
    } else if n % 2 == 1 {
        false
    } else {
        is_power_of_two(n / 2)
    }
}

spec fn valid_input(n: int) -> bool {
    n >= 1
}

spec fn correct_result(n: int, result: int) -> bool {
    if n % 2 == 1 {
        result == (n - 1) / 2
    } else {
        exists|z: int| 1 <= z <= n && is_power_of_two(z) && z <= n && z * 2 > n && result == (n - z) / 2
    }
}
// </vc-helpers>

// <vc-spec>
fn solve(n: int) -> (result: int)
    requires valid_input(n)
    ensures correct_result(n, result)
// </vc-spec>
// <vc-code>
{
    // impl-start
    assume(false);
    unreached()
    // impl-end
}
// </vc-code>


}

fn main() {}