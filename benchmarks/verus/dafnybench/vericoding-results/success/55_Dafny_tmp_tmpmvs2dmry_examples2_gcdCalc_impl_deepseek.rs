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
proof fn gcd_terminates(a: nat, b: nat)
    requires a > 0 && b > 0
    decreases a + b
{
    if a != b {
        if a > b {
            gcd_terminates( (a - b) as nat, b);
        } else {
            gcd_terminates(a, (b - a) as nat);
        }
    }
}

proof fn gcd_commutative(m: nat, n: nat)
    requires m > 0 && n > 0
    ensures gcd(m, n) == gcd(n, m)
    decreases m + n
{
    if m != n {
        if m > n {
            gcd_commutative((m - n) as nat, n);
            gcd_commutative(n, (m - n) as nat);
        } else {
            gcd_commutative(m, (n - m) as nat);
            gcd_commutative((n - m) as nat, m);
        }
    }
}
// </vc-helpers>

// <vc-spec>
fn gcd_calc(m: u32, n: u32) -> (res: u32)
    requires m > 0 && n > 0
    ensures res == gcd(m as nat, n as nat)
// </vc-spec>
// <vc-code>
{
    let mut a: u32 = m;
    let mut b: u32 = n;
    
    proof { gcd_terminates(a as nat, b as nat); }
    
    while a != b
        invariant 
            a > 0 && b > 0,
            gcd(a as nat, b as nat) == gcd(m as nat, n as nat)
        decreases a + b
    {
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