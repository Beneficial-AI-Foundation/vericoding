use vstd::prelude::*;

verus! {

spec fn power(n: nat) -> nat
    decreases n
{
    if n == 0 { 1 } else { 2 * power((n - 1) as nat) }
}

// <vc-helpers>
spec fn double(n: nat) -> nat
    decreases n
{
    n * 2
}

 proof fn power_is_double(n: nat)
    decreases n
{
    if n != 0 {
        power_is_double((n - 1) as nat);
        reveal_with_fuel(power, 1);
        assert(power(n) == 2 * power((n - 1) as nat));
        assert(power(n) == double(power((n - 1) as nat)));
    }
}

 proof fn power_monotonic(n1: nat, n2: nat)
    requires n1 <= n2
    ensures power(n1) <= power(n2)
    decreases n2 - n1
{
    if n1 < n2 {
        reveal_with_fuel(power, 2);
        assert(power(n1+1) == 2 * power(n1));
        assert(2 * power(n1) >= power(n1));
        power_monotonic(n1 + 1, n2);
    }
}
// </vc-helpers>

// <vc-spec>
fn compute_power(n: u32) -> (p: u32)
    requires n < 32, // practical bound to prevent overflow
    ensures p == power(n as nat),
// </vc-spec>
// <vc-code>
{
    let result = 1u32;
    let i = 0;
    while i < n
        invariant
            i <= n,
            result == power(i as nat),
            result <= power(n as nat)
    {
        result = result * 2;
        i = i + 1;
        proof {
            power_monotonic(i as nat, n as nat);
        }
    }
    result
}
// </vc-code>

fn main() {
}

}