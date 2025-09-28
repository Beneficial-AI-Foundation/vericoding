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
proof fn power_succ(n: nat) {
    // By definition of `power`
    assert(power(n + 1) == 2 * power(n));
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
        invariant i <= n;
        invariant (p as nat) == power(i as nat);
        decreases (n - i) as nat;
    {
        let old_i = i;
        let old_p = p;
        p = p * 2;
        i = i + 1;
        proof {
            // preserve the invariant: old_p corresponds to power(old_i)
            assert((old_p as nat) == power(old_i as nat));
            // loop condition ensured old_i < n
            assert(old_i < n);
            // i was incremented
            assert(i == old_i + 1);
            // p updated to twice old_p
            assert((p as nat) == 2 * (old_p as nat));
            // use lemma about power
            power_succ(old_i as nat);
            // combine equalities to re-establish invariant for new i
            assert((p as nat) == power(i as nat));
        }
    }

    p
}
// </vc-code>

fn main() {
}

}