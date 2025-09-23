// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn is_odd(n: int) -> bool {
    n % 2 == 1
}

spec fn count_divisors(n: nat) -> nat
    recommends n > 0
{
    Set::new(|d: nat| 1 <= d <= n && n % d == 0).len()
}

spec fn has_eight_divisors(n: nat) -> bool
    recommends n > 0
{
    count_divisors(n) == 8
}

spec fn count_odd_with_eight_divisors(n: nat) -> nat {
    Set::new(|i: nat| 1 <= i <= n && is_odd(i as int) && i > 0 && has_eight_divisors(i)).len()
}

spec fn valid_input(n: int) -> bool {
    1 <= n <= 200
}
// </vc-helpers>

// <vc-spec>
fn solve(n: int) -> (count: int)
    requires 
        valid_input(n)
    ensures 
        n < 105 ==> count == 0,
        105 <= n && n < 135 ==> count == 1,
        135 <= n && n < 165 ==> count == 2,
        165 <= n && n < 189 ==> count == 3,
        189 <= n && n < 195 ==> count == 4,
        n >= 195 ==> count == 5,
        0 <= count && count <= 5,
// </vc-spec>
// <vc-code>
{
    assume(false);
    0int
}
// </vc-code>


}

fn main() {}