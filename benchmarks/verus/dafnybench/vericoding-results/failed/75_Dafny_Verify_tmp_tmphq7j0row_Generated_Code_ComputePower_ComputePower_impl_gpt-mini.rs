use vstd::prelude::*;

verus! {

spec fn power(n: nat) -> nat
    decreases n
{
    if n == 0 { 1 } else { 2 * power((n - 1) as nat) }
}

// <vc-helpers>
proof fn power_succ(n: nat)
    ensures power(n + 1) == 2 * power(n)
    decreases n
{
    if n == 0 {
        assert(power(1) == 2 * power(0));
    } else {
        assert(power(n + 1) == 2 * power(n));
    }
}

proof fn shift_power(n: nat)
    ensures ((1u32 << (n as u32)) as nat) == power(n)
    decreases n
{
    if n == 0 {
        assert((1u32 << 0) == 1u32);
        assert(((1u32 << 0) as nat) == power(0));
    } else {
        shift_power(n - 1);
        // For n > 0: (1 << n) == (1 << (n-1)) * 2
        let lhs: u32 = 1u32 << (n as u32);
        let prev: u32 = 1u32 << ((n - 1) as u32);
        assert(lhs == prev * 2u32);
        assert((lhs as nat) == 2 * ((prev as nat)));
        assert((lhs as nat) == 2 * power(n - 1));
        assert((lhs as nat) == power(n));
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
    let p: u32 = 1u32 << n;
    proof {
        shift_power(n as nat);
        assert((p as nat) == power(n as nat));
    }
    p
}
// </vc-code>

fn main() {
}

}