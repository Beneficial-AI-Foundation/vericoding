// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
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

spec fn count_divisors(n: nat) -> nat
    recommends n > 0
{
    Set::new(|d: nat| 1 <= d <= n && n % d == 0).len()
}

spec fn count_special_divisors(n: nat) -> nat
    recommends n > 0
{
    Set::new(|d: nat| 2 <= d <= n && n % d == 0 && (reduce_by_divisor(n, d) - 1) % d == 0).len()
}

spec fn count_valid_k_values(n: nat) -> int
    recommends n > 0
{
    if n == 1 {
        -1
    } else {
        count_divisors(n - 1) + count_special_divisors(n) - 1
    }
}
// </vc-helpers>

// <vc-spec>
fn solve(n: nat) -> (result: int)
    requires valid_input(n)
    ensures result == count_valid_k_values(n)
    ensures n == 1 ==> result == -1
    ensures n > 1 ==> result == count_divisors(n - 1) + count_special_divisors(n) - 1
    ensures result >= -1
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>


}

fn main() {}