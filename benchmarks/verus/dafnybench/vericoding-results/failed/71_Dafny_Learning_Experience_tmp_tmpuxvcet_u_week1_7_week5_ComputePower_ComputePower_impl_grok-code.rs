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
// auxiliary code and proofs 
// </vc-helpers>
// </vc-helpers>

// <vc-spec>
fn compute_power(n: u32) -> (p: u32)
    ensures p == power(n as nat)
// </vc-spec>
// <vc-code>
{
    let mut result = 1u32;
    let mut i = 0;
    while i < n {
        invariant i <= n;
        invariant result == power(i as nat);
        decreases n - i;
        result = result * 2;
        i = i + 1;
    }
    result
}
// </vc-code>

fn main() {
}

}