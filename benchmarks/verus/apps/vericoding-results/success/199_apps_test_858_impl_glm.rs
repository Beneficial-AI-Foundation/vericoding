// <vc-preamble>
use vstd::prelude::*;

verus! {
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
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): changed to use i8 instead of int to avoid ghost type in non-ghost code */
fn largest_power_of_two(n: i8) -> (result: i8)
    requires n >= 1
    ensures is_power_of_two(result as int) && result as int <= n as int && (result as int) * 2 > n as int
{
    let mut z: i8 = 1;
    while z <= n / 2
        invariant 1 <= z <= n && is_power_of_two(z as int)
        decreases (n - z) as int
    {
        z = z * 2;
    }
    z
}
// </vc-helpers>

// <vc-spec>
fn solve(n: i8) -> (result: i8)
    requires valid_input(n as int)
    ensures correct_result(n as int, result as int)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): removed conversion to int, use i8 arithmetic throughout */
    if n % 2 == 1 {
        let res = (n - 1) / 2;
        res
    } else {
        let z = largest_power_of_two(n);
        let res = (n - z) / 2;
        res
    }
}
// </vc-code>


}

fn main() {}