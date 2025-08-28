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
proof fn lemma_power_bounds(n: nat)
    ensures power(n) >= 1
    decreases n
{
    if n == 0 {
    } else {
        lemma_power_bounds((n - 1) as nat);
    }
}

proof fn lemma_power_u32_bounds(n: u32)
    requires n <= 30
    ensures power(n as nat) <= 0x80000000
    decreases n
{
    if n == 0 {
    } else {
        lemma_power_u32_bounds(n - 1);
        assert(power(n as nat) == 2 * power((n - 1) as nat));
    }
}
// </vc-helpers>

// <vc-spec>
// <vc-spec>
fn compute_power(n: u32) -> (p: u32)
    ensures p == power(n as nat)
// </vc-spec>
// </vc-spec>

// <vc-code>
{
    lemma_power_u32_bounds(n);
    
    let mut result: u32 = 1;
    let mut i: u32 = 0;
    
    while i < n
        invariant 0 <= i <= n
        invariant result == power(i as nat)
        invariant result <= 0x80000000
    {
        result = result * 2;
        i = i + 1;
    }
    
    result
}
// </vc-code>

fn main() {
}

}