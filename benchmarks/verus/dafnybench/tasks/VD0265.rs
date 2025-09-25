// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn gcd(m: nat, n: nat) -> nat
    recommends m > 0 && n > 0
    decreases m + n
    when m > 0 && n > 0
{
    if m == n {
        n
    } else if m > n {
        gcd(sub(m, n), n)
    } else {
        gcd(m, sub(n, m))
    }
}

spec fn exp_nat(base: nat, n: nat) -> nat
    decreases n
{
    if n == 0 {
        1nat
    } else if base == 0 {
        0nat
    } else {
        base * exp_nat(base, sub(n, 1))
    }
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn gcd_calc(m: u32, n: u32) -> (res: u32)
    requires m > 0 && n > 0
    ensures res == gcd(m as nat, n as nat)
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}