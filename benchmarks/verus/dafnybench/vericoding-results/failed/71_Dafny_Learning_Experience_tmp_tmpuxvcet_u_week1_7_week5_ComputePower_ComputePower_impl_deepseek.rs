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
spec fn power_lemma(n: nat, m: nat)
    decreases n
    ensures power(n) * power(m) == power(n + m)
{
    if n > 0 {
        power_lemma((n - 1) as nat, m);
        assert(power(n) == 2 * power((n - 1) as nat));
        assert(power(n + m) == 2 * power((n + m - 1) as nat));
    }
}

proof fn power_zero() 
    ensures power(0) == 1
{
}

proof fn power_nonzero(n: nat)
    requires n > 0
    ensures power(n) == 2 * power((n - 1) as nat)
{
}

proof fn power_always_positive(n: nat)
    ensures power(n) > 0
    decreases n
{
    if n > 0 {
        power_always_positive((n - 1) as nat);
    }
}
// </vc-helpers>

// <vc-spec>
fn compute_power(n: u32) -> (p: u32)
    ensures p == power(n as nat)
// </vc-spec>
// <vc-code>
{
    if n == 0 {
        proof { power_zero(); }
        1
    } else {
        let prev = compute_power(n - 1);
        proof { 
            power_nonzero(n as nat);
        }
        2 * prev
    }
}
// </vc-code>

fn main() {
}

}