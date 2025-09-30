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
/* helper modified by LLM (iteration 4): loop uses i8 arithmetic and avoids int casts */
fn largest_power_of_two_le(n: i8) -> (z: i8)
    requires
        n >= 1,
    ensures
        1 <= z && z <= n && is_power_of_two(z as int) && (z as int) * 2 > (n as int),
    decreases
        n,
{
    let mut z: i8 = 1;
    while z <= n / 2
        invariant
            1 <= z,
            is_power_of_two(z as int),
            z <= n,
        decreases
            (n as int) - (z as int)
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
/* code modified by LLM (iteration 4): compute result using helper and handle odd/even n */
{
    if n % 2 != 0 {
        let r: i8 = (n - 1) / 2;
        return r;
    }
    let z: i8 = largest_power_of_two_le(n);
    let r: i8 = (n - z) / 2;
    r
}

// </vc-code>


}

fn main() {}