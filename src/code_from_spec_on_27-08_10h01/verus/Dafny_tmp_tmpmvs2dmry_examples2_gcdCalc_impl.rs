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

// <vc-helpers>
proof fn gcd_properties(m: nat, n: nat)
    requires m > 0 && n > 0
    ensures gcd(m, n) > 0
    decreases m + n
{
    if m == n {
    } else if m > n {
        gcd_properties(sub(m, n), n);
    } else {
        gcd_properties(m, sub(n, m));
    }
}

proof fn gcd_symmetric(m: nat, n: nat)
    requires m > 0 && n > 0
    ensures gcd(m, n) == gcd(n, m)
    decreases m + n
{
    if m == n {
    } else if m > n {
        gcd_symmetric(sub(m, n), n);
        gcd_symmetric(n, sub(m, n));
    } else {
        gcd_symmetric(m, sub(n, m));
        gcd_symmetric(sub(n, m), m);
    }
}
// </vc-helpers>

// <vc-spec>
// <vc-spec>
fn gcd_calc(m: u32, n: u32) -> (res: u32)
    requires m > 0 && n > 0
    ensures res == gcd(m as nat, n as nat)
// </vc-spec>
// </vc-spec>

// <vc-code>
{
    let mut a = m;
    let mut b = n;
    
    while a != b
        invariant a > 0 && b > 0
        invariant gcd(a as nat, b as nat) == gcd(m as nat, n as nat)
        decreases a + b
    {
        proof {
            gcd_properties(a as nat, b as nat);
        }
        if a > b {
            a = a - b;
        } else {
            b = b - a;
        }
    }
    
    a
}
// </vc-code>

fn main() {}

}