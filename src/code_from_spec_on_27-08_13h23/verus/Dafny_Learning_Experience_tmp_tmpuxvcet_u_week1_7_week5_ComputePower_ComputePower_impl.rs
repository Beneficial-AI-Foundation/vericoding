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
proof fn lemma_power(n: nat)
    decreases n
    ensures power(n) == if n == 0 { 1 } else { 2 * power((n - 1) as nat) }
{
    if n == 0 {
        assert(power(0) == 1);
    } else {
        lemma_power((n - 1) as nat);
        assert(power(n) == 2 * power((n - 1) as nat));
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
fn compute_power(n: u32) -> (p: u32)
    ensures p == power(n as nat)
{
    let mut result: u32 = 1;
    let mut i: u32 = 0;
    
    while i < n
        invariant
            i <= n,
            result == power(i as nat)
    {
        result = result * 2;
        i = i + 1;
        proof {
            lemma_power(i as nat);
        }
    }
    
    result
}
// </vc-code>

fn main() {
}

}