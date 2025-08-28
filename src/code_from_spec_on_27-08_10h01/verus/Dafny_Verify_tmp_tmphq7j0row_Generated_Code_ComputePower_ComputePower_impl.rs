use vstd::prelude::*;

verus! {

spec fn power(n: nat) -> nat
    decreases n
{
    if n == 0 { 1 } else { 2 * power((n - 1) as nat) }
}

// <vc-helpers>
proof fn power_monotonic(n: nat)
    ensures power(n + 1) == 2 * power(n)
{
}

proof fn power_bounds(n: nat)
    requires n < 32
    ensures power(n) < 0x100000000
    decreases n
{
    if n == 0 {
    } else {
        power_bounds((n - 1) as nat);
        assert(power(n) == 2 * power((n - 1) as nat));
    }
}
// </vc-helpers>

// <vc-spec>
// <vc-spec>
fn compute_power(n: u32) -> (p: u32)
    requires n < 32, // practical bound to prevent overflow
    ensures p == power(n as nat),
// </vc-spec>
// </vc-spec>

// <vc-code>
{
    proof {
        power_bounds(n as nat);
    }
    
    if n == 0 {
        1
    } else {
        let prev = compute_power(n - 1);
        proof {
            assert(prev == power((n - 1) as nat));
            assert(power(n as nat) == 2 * power((n - 1) as nat));
        }
        2 * prev
    }
}
// </vc-code>

fn main() {
}

}