use vstd::prelude::*;

verus! {

spec fn power(n: nat) -> nat
    decreases n
{
    if n == 0 { 1 } else { 2 * power((n - 1) as nat) }
}

// <vc-helpers>
// Empty - no additional helpers needed
// </vc-helpers>

// <vc-spec>
fn compute_power(n: u32) -> (p: u32)
    requires n < 32, // practical bound to prevent overflow
    ensures p == power(n as nat),
// </vc-spec>
// <vc-code>
{
    let mut p = 1u64;
    let mut i = 0u32;
    proof {
        assert(power(0 as nat) == 1);
    }
    while i < n
        decreases ((n as int) - (i as int))
        invariant 0 <= i <= n
        invariant p as nat == power(i as nat)
        invariant p <= 2147483648 // 2^31, max value for n<32
    {
        proof {
            assert(power((i + 1) as nat) == 2 * power(i as nat));
            assert(2 * (p as nat) == 2 * power(i as nat));
            assert(2 * (p as nat) == power((i + 1) as nat));
        }
        p = p * 2;
        i = i + 1;
    }
    proof {
        assert(p as nat == power(n as nat));
        assert(p <= 2147483648);
        assert(p < 4294967296); // 2^32, within u32 range
    }
    p as u32
}
// </vc-code>

fn main() {
}

}