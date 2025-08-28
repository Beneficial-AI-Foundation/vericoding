use vstd::prelude::*;

verus! {

//Problem01
spec fn fib(n: nat) -> nat
    decreases n
{
    if n < 2 { n } else { fib((n-2) as nat) + fib((n-1) as nat) }
}

//# 2 pts

//Problem02
spec fn fact(n: nat) -> nat
    decreases n
{
    if n == 0 { 1 } else { n * fact((n-1) as nat) }
}

//# 3 pts
//Problem03
spec fn gcd(m: nat, n: nat) -> nat
    decreases (m + n)
{
    if m == 0 || n == 0 { 0 }
    else if m == n { m }
    else if m > n { gcd((m - n) as nat, n) }
    else { gcd(m, (n - m) as nat) }
}

// <vc-helpers>
proof fn gcd_comm(m: nat, n: nat)
    ensures gcd(m, n) == gcd(n, m)
    decreases m + n
{
    if m == 0 || n == 0 {
        // Base case
    } else if m == n {
        // Base case: gcd(m, m) == gcd(m, m)
    } else if m > n {
        gcd_comm((m - n) as nat, n);
        gcd_comm(n, (m - n) as nat);
    } else {
        gcd_comm(m, (n - m) as nat);
        gcd_comm((n - m) as nat, m);
    }
}

proof fn gcd_subtract_property(m: nat, n: nat)
    requires m > 0 && n > 0 && m > n
    ensures gcd(m, n) == gcd((m - n) as nat, n)
    decreases m + n
{
    // This follows from the definition of gcd
}

proof fn gcd_zero_case(m: nat, n: nat)
    requires m == 0 || n == 0
    ensures gcd(m, n) == 0
{
    // Follows from definition
}

proof fn gcd_invariant_maintains(m: nat, n: nat, new_m: nat, new_n: nat)
    requires m > 0 && n > 0
    requires (new_m == (m - n) as nat && new_n == n && m > n) || 
             (new_m == m && new_n == (n - m) as nat && n > m)
    ensures gcd(m, n) == gcd(new_m, new_n)
{
    if m > n {
        gcd_subtract_property(m, n);
    } else {
        gcd_comm(m, n);
        gcd_subtract_property(n, m);
        gcd_comm((n - m) as nat, m);
    }
}
// </vc-helpers>

// <vc-spec>
// <vc-spec>
fn gcd_iterative(m: u32, n: u32) -> (g: u32)
    requires m > 0 && n > 0
    ensures g == gcd(m as nat, n as nat);
// </vc-spec>
// </vc-spec>

// <vc-code>
fn gcd_iterative(m: u32, n: u32) -> (g: u32)
    requires m > 0 && n > 0
    ensures g == gcd(m as nat, n as nat)
{
    let mut a = m;
    let mut b = n;
    
    while a != b
        invariant a > 0 && b > 0
        invariant gcd(a as nat, b as nat) == gcd(m as nat, n as nat)
        decreases a + b
    {
        if a > b {
            proof {
                gcd_invariant_maintains(a as nat, b as nat, (a - b) as nat, b as nat);
            }
            a = a - b;
        } else {
            proof {
                gcd_invariant_maintains(a as nat, b as nat, a as nat, (b - a) as nat);
            }
            b = b - a;
        }
    }
    
    proof {
        assert(a == b);
        assert(gcd(a as nat, b as nat) == a);
    }
    
    a
}
// </vc-code>

//# 3 pts


// # sum: 9 pts

fn main() {
}

}