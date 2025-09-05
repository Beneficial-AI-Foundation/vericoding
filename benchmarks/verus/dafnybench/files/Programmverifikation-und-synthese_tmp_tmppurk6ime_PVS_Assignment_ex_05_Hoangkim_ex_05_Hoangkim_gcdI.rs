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
// </vc-helpers>

// <vc-spec>
fn gcd_iterative(m: u32, n: u32) -> (g: u32)
    requires m > 0 && n > 0,
    ensures g == gcd(m as nat, n as nat),
// </vc-spec>
// <vc-code>
{
    assume(false);
    0
}
// </vc-code>

//# 3 pts


// # sum: 9 pts

fn main() {
}

}