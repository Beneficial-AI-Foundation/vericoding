use vstd::prelude::*;

verus! {

spec fn power(n: nat) -> nat
    decreases n
{
    if n == 0 { 1 } else { 2 * power((n - 1) as nat) }
}

// <vc-helpers>
spec fn spec_pow2_u32(n: u32) -> u32
    decreases n
{
    if n == 0 { 1 } else { 2 * spec_pow2_u32((n - 1) as u32) }
}
// </vc-helpers>

// <vc-spec>
fn compute_power(n: u32) -> (p: u32)
    requires n < 32, // practical bound to prevent overflow
    ensures p == power(n as nat),
// </vc-spec>
// <vc-code>
{
    let mut i: u32 = 0;
    let mut p: u32 = 1;

    while i < n
        invariant
            i <= n,
            p == spec_pow2_u32(i),
            p == power(i as nat),
        decreases (n - i)
    {
        i = i + 1;
        p = p * 2;
    }
    p
}
// </vc-code>

fn main() {
}

}