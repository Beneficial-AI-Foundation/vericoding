// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(n: nat) -> bool {
    n > 0
}

spec fn reduce_by_divisor(n: nat, d: nat) -> nat
    recommends n > 0 && d > 1
    decreases n
{
    if n % d == 0 && n >= d { 
        reduce_by_divisor(n / d, d)
    } else {
        n
    }
}

spec fn count_divisors(n: int) -> nat
    recommends n > 0
{
    Set::new(|d: int| 1 <= d <= n && n % d == 0).len()
}

spec fn count_special_divisors(n: nat) -> nat
    recommends n > 0
{
    Set::new(|d: int| 2 <= d <= n && (n as int) % d == 0 && (reduce_by_divisor(n, d as nat) as int - 1) % d == 0).len()
}

spec fn count_valid_k_values(n: nat) -> int
    recommends n > 0
{
    if n == 1 { 
        -1
    } else {
        count_divisors(n as int - 1) as int + count_special_divisors(n) as int - 1
    }
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn solve(n: nat) -> (result: int)
    requires valid_input(n)
    ensures 
        result == count_valid_k_values(n) &&
        (n == 1 ==> result == -1) &&
        (n > 1 ==> result == count_divisors(n as int - 1) as int + count_special_divisors(n) as int - 1) &&
        result >= -1
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>


}

fn main() {}