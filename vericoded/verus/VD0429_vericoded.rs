// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn fib(n: nat) -> nat
    decreases n
{
    if n < 2 { n } else { fib((n-2) as nat) + fib((n-1) as nat) }
}

spec fn fact(n: nat) -> nat
    decreases n
{
    if n == 0 { 1 } else { n * fact((n-1) as nat) }
}

spec fn gcd(m: nat, n: nat) -> nat
    decreases (m + n)
{
    if m == 0 || n == 0 { 0 }
    else if m == n { m }
    else if m > n { gcd((m - n) as nat, n) }
    else { gcd(m, (n - m) as nat) }
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn gcd_iterative(m: u32, n: u32) -> (g: u32)
    requires m > 0 && n > 0,
    ensures g == gcd(m as nat, n as nat),
// </vc-spec>
// <vc-code>
{
    let mut a = m;
    let mut b = n;
    while a != b
        invariant
            a > 0,
            b > 0,
            gcd(a as nat, b as nat) == gcd(m as nat, n as nat),
        decreases (a as nat) + (b as nat)
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

}
fn main() {}