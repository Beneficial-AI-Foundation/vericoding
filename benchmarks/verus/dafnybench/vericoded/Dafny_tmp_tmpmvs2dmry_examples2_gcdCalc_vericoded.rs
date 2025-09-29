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
        assert(gcd(m, n) == n);
        assert(n > 0);
    } else if m > n {
        gcd_properties(sub(m, n), n);
        assert(gcd(sub(m, n), n) > 0);
        assert(gcd(m, n) == gcd(sub(m, n), n));
    } else {
        gcd_properties(m, sub(n, m));
        assert(gcd(m, sub(n, m)) > 0);
        assert(gcd(m, n) == gcd(m, sub(n, m)));
    }
}

proof fn gcd_step_equivalence(m: nat, n: nat)
    requires m > 0 && n > 0
    ensures 
        m > n ==> gcd(m, n) == gcd(sub(m, n), n),
        n > m ==> gcd(m, n) == gcd(m, sub(n, m))
{
    // The equivalence follows directly from the definition of gcd
}
// </vc-helpers>

// <vc-spec>
fn gcd_calc(m: u32, n: u32) -> (res: u32)
    requires m > 0 && n > 0
    ensures res == gcd(m as nat, n as nat)
// </vc-spec>
// <vc-code>
{
    let mut a = m;
    let mut b = n;
    
    while a != b
        invariant 
            a > 0,
            b > 0,
            gcd(a as nat, b as nat) == gcd(m as nat, n as nat)
        decreases a + b
    {
        proof {
            gcd_step_equivalence(a as nat, b as nat);
        }
        
        if a > b {
            a = a - b;
        } else {
            b = b - a;
        }
    }
    
    proof {
        assert(a == b);
        assert(gcd(a as nat, b as nat) == a as nat);
        assert(gcd(m as nat, n as nat) == a as nat);
    }
    
    a
}
// </vc-code>

fn main() {}

}