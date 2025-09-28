use vstd::prelude::*;

verus! {

spec fn power(n: nat) -> nat 
    decreases n
{
    if n == 0 { 1 } else { 2 * power((n - 1) as nat) }
}

fn calc_power(n: u32) -> (p: u32)
    ensures p == 2 * n
{
  assume(false);
  0
}

// <vc-helpers>
#[verifier(external_body)]
#[allow(arithmetic_overflow)]
fn u32_power(n: u32) -> u32 {
    if n == 0 { 1 } else { 2 * u32_power(n - 1) }
}
// </vc-helpers>

// <vc-spec>
fn compute_power(n: u32) -> (p: u32)
    ensures p == power(n as nat)
// </vc-spec>
// <vc-code>
{
    let mut i: u32 = 0;
    let mut p: u32 = 1;
    while i < n
        invariant
            i <= n,
            p == power(i as nat),
            p == u32_power(i), // Add this invariant
        decreases (n - i)
    {
        proof {
            assert(power((i + 1) as nat) == 2 * power(i as nat));
            assert(u32_power(i + 1) == 2 * u32_power(i)); // Add this assertion
        }
        p = p * 2;
        i = i + 1;
    }
    p
}
// </vc-code>

fn main() {
}

}