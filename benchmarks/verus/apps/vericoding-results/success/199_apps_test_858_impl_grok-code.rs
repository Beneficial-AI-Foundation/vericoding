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
fn find_largest_power_of_two(n: i8) -> (result: i8)
    requires n >= 1
    ensures
        1 <= result as int <= n as int,
        is_power_of_two(result as int),
        (n as int % 2 == 0) ==> (result as int * 2 > n as int),
{
    /* helper modified by LLM (iteration 3): removed redundant invariant condition to satisfy loop checks */
    let mut p: i32 = 1;
    while 2 as i32 * (p as i32) <= n as i32
        invariant
            1 <= p as int,
            is_power_of_two(p as int),
            p as int <= n as int,
        decreases n as int - p as int
    {
        p = 2 as i32 * (p as i32);
    }
    p as i8
}
// </vc-helpers>

// <vc-spec>
fn solve(n: i8) -> (result: i8)
    requires valid_input(n as int)
    ensures correct_result(n as int, result as int)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): added asserts for spec function proof */
    if n % 2 == 1 {
        let res: i8 = (n - 1) / 2;
        proof {
            assert(correct_result(n as int, res as int));
        }
        res
    } else {
        let z = find_largest_power_of_two(n);
        let res: i8 = (n - z) / 2;
        proof {
            let w = z as int;
            assert(1 <= w <= n as int);
            assert(is_power_of_two(w));
            assert(w * 2 > n as int);
            assert(res as int == (n as int - w) / 2);
            assert(correct_result(n as int, res as int));
        }
        res
    }
}
// </vc-code>


}

fn main() {}