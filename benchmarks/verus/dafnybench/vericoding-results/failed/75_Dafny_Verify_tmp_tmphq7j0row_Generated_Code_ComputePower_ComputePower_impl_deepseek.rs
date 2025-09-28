use vstd::prelude::*;

verus! {

spec fn power(n: nat) -> nat
    decreases n
{
    if n == 0 { 1 } else { 2 * power((n - 1) as nat) }
}

// <vc-helpers>
proof fn lemma_power_zero()
    ensures power(0) == 1,
{
}

proof fn lemma_power_step(n: nat)
    requires
        n > 0,
    ensures
        power(n) == 2 * power((n - 1) as nat),
    decreases n,
{
}

proof fn lemma_power_exists(n: nat)
    ensures
        exists|p: nat| power(n) == p,
    decreases n,
{
    reveal(power);
    if n == 0 {
    } else {
        lemma_power_exists((n - 1) as nat);
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
    let mut p: u32 = 1;
    let mut i: u32 = 0;
    while i < n
        invariant
            i <= n,
            p == power(i as nat),
        decreases n - i,
    {
        p = p * 2;
        i = i + 1;
        proof {
            lemma_power_step(i as nat);
        }
    }
    p
}
// </vc-code>

fn main() {
}

}